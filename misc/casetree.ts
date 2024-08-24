// why I'm not doing this in a real language, I don't know

// It might be interesting to add some types and flesh this out
// but time may be better spent on the real deal (where I have easy
// access to types)

// the array version is always a constructor application
type Pattern = string | [string, ...Pattern[]];
type Constraint = [Pattern, Pattern];
type Exp = string | Exp[];

type Clause = [Constraint[], Pattern[], Exp];
type Problem = Clause[];

type Tree =
  | ["Lam", string, Tree]
  | ["Done", Exp]
  | ["Case", string, [string[], Tree][]];

// These are essentially sexpr
const showExp = (exp: Exp): string => {
  if (exp instanceof Array) {
    return "(" + exp.map(showExp).join(" ") + ")";
  }
  return exp;
};

const printProb = (prob: Problem) => {
  for (let [cs, ps, exp] of prob) {
    console.log(
      `[${cs
        .map(([a, b]) => `${showExp(a)} /? ${showExp(b)}`)
        .join(", ")}] ${ps} => ${showExp(exp)}`
    );
  }
};

const printTree = (tree: Tree, indent = "") => {
  switch (tree[0]) {
    case "Lam":
      console.log(indent + "Lam", tree[1]);
      printTree(tree[2], indent + "  ");
      break;
    case "Done":
      console.log(indent, showExp(tree[1]));
      break;
    case "Case":
      console.log(indent + "Case", tree[1]);
      for (let [l, r] of tree[2]) {
        console.log(indent + "  " + showExp(l), "=>");
        printTree(r, indent + "    ");
      }
      break;
    default:
      console.log("FIXME");
  }
};

let problem: Problem = [
  [[], [["Z"], "j"], "j"],
  [[], ["i", ["Z"]], "i"],
  [
    [],
    [
      ["S", "k"],
      ["S", "l"],
    ],
    ["S", ["max", "k", "l"]],
  ],
];
let next = 0;
const free = () => "i" + next++;

// intro applies if everybody has shape [n, ...ns]
function intro(prob: Problem): Tree {
  let name = free();
  console.log("INTRO", name);
  let prob2: Problem = prob.map(([cs, [n, ...ns], exp]) => [
    [...cs, [name, n]],
    ns,
    exp,
  ]);
  printProb(prob2);
  return ["Lam", name, solve(prob2)];
}

function substPat(prob: Problem, name: string, pat: Pattern): Tree {
  console.log("subproblem", pat);
  let prob2: Problem = [];
  OUTER: for (let [cs, ps, exp] of prob) {
    let cs2: Constraint[] = [];
    for (let [a, b] of cs) {
      if (a === name) {
        if (b instanceof Array) {
          if (b[0] !== pat[0]) {
            console.log("drop mismatch", pat, "/?", b);
            // drop entire clause
            continue OUTER;
          } else {
            console.log("zip");
            // zip
            if (pat.length !== b.length) {
              console.error("length mismatch", pat, "/?", b);
              throw new Error();
            }
            for (let i = 1; i < pat.length; i++) {
              cs2.push([pat[i], b[i]]);
            }
          }
          // REVIEW can name occur anywhere else?
        } else {
          cs2.push([pat, b]);
        }
      } else {
        cs2.push([a, b]);
      }
    }
    prob2.push([cs2, ps, exp]);
  }

  printProb(prob2);
  return solve(prob2);
}

function split(prob: Problem, name: string): Tree {
  console.log("SPLIT", name);
  // here we're assuming Nat for our example
  let arg = free();
  return [
    "Case",
    name,
    [
      [["Z"], substPat(prob, name, ["Z"])],
      [["S", arg], substPat(prob, name, ["S", arg])],
    ],
  ];
}

const canIntro = (prob: Problem) => prob.every((cl) => cl[1].length);

console.log(canIntro(problem));

function subst(exp: Exp, x: string, y: Pattern): Exp {
  if (exp === x) return y;
  if (typeof exp === "string") return exp;
  return exp.map((e) => subst(e, x, y));
}

function solve(prob: Problem): Tree {
  if (canIntro(prob)) return intro(prob);

  // Done if no copattern and constraints all solved on first clause...

  // SplitCon if first clause has a x /? c p1... with x having appropriate type
  let [cs, ps, exp] = prob[0];
  let cs2: Constraint[] = [];
  for (let [x, y] of cs) {
    // need to check types too
    if (y instanceof Array && typeof x === "string") {
      return split(prob, x);
    }
    // subst and see if there is anything left.
    if (typeof y === "string") {
      exp = subst(exp, y, x);
    } else {
      cs2.push([x, y]);
    }
  }
  if (!cs2.length && !ps.length) return ["Done", exp];

  // SplitEmpty if first clause has a x /? ø with x of empty type

  // SplitEq if first clause has a x /? refl with appropriate type
  // here a substitution is generated from the unification of the refl

  printProb(prob);
  throw new Error(`stuck`);
}

printTree(intro(problem));
