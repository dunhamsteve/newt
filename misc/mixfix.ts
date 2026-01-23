// mixfix+pratt experiment, single expression type
// Generates ["app", "a", "b"] nodes for app

// 561 bytes w/o test cases, error messages

// TODO
// - it might be interesting to pretty print stuff back using the grammar

// using a tuple makes the output two bytes bigger...
type OpDef = { n: string; p: number; f: string; s: string[] }
type Rules = Record<string, OpDef>
type AST = string | AST[]

function parse(str: string, grammar: string) {
  let rval
  let rules: Rules = {}
  let fail = (m?: string) => {
    throw new Error(m)
  }
  // Fancy tokenizer
  let toks = str.match(/\w+|[=>+*/-]+|\d+|\S/g)!
  let pos = 0
  let mixfix = (ast: AST[], def: OpDef, stop: string): AST => {
    def.s.slice(def.s[0] ? 1 : 2).forEach((step) => {
      ast.push(step ? expr(0, step) : expr(def.f == 'L' ? def.p + 1 : def.p, stop))
      if (step && toks[pos++] != step) fail('expected ' + step)
    })
    return ast
  }

  let expr = (prec: number, stop: string): AST => {
    // this needs to be an arg for tail recursive version
    let left: AST = toks[pos++]
    let right: AST
    let rule = rules[left as string]
    if (!left) fail('EOF')
    if (rule) left = rule.s[0] ? mixfix([rule.n], rule, stop) : fail('stray operator')
    for (;;) {
      right = toks[pos]
      if (!right || right == stop) return left
      rule = rules[right]
      if (!rule) {
        left = ['app', left, right]
        pos++
      } else if (rule.s[0]) {
        pos++
        left = ['app', left, mixfix([rule.n], rule, stop)]
      } else {
        if (rule.p < prec) return left
        pos++
        left = mixfix([rule.n, left], rule, stop)
      }
    }
  }
  // Parse grammar
  grammar
    .trim()
    .split('\n')
    .forEach((def) => {
      let [fix, prec, name] = def.split(' ')
      let parts = name.split('_')
      rules[parts[0] || parts[1]] = { n: name, p: +prec, f: fix, s: parts }
    })

  // need to check if we've parsed everything
  rval = expr(0, '')
  if (toks[pos]) fail(`extra toks`)
  return rval
}

// TESTS

// For prefix, the tail gets the prec
let grammar = `
R 7 _++_
L 7 _+_
L 7 _-_
L 8 _*_
L 8 _/_
L 1 _==_
L 0 (_)
R 0 if_then_else_
R 0 \\_=>_
`

const check = (s: string) => console.log(s, ' -> ', parse(s, grammar))
const failing = (s: string) => {
  let rval
  try {
    rval = parse(s, grammar)
  } catch (e) {
    console.log(s, ' ->', e!.toString())
  }
  if (rval) throw new Error(`expected ${s} to fail, got ${JSON.stringify(rval)}`)
}
check('a b c')
check('1+1')
check('\\ x => x')
check('a+b+c')
check('a++b++c')
check('a+b*c+d')
check('(a+b)*c')
check('if x == 1 + 1 then a + b else c')
check('1 ∧ 2')
check('a b + b c')
check('¬ a')
failing('a +')
failing('a + +')
failing('+ a')

// Has to be at end because TESTS

// for "minify", I'm dropping error details and using map instead of forEach
// sed -e 's/fail([^)]*)/fail()/g;s/forEach/map/g;/TESTS/,$d' <src/mixfix.ts|esbuild --loader=ts --minify|wc -c
