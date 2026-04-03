// We're going to do the VDom thing, directly off of newt data

type Attrib<Msg> =
  | { tag: 0; h1: string; h2: string }
  | { tag: 1; h1: string; h2: Msg }
  | { tag: 2; h1: string; h2: (_: string) => Msg };

type List<A> = { tag: 0 } | { tag: 1; h1: A; h2: List<A> };

type VNode<Msg> =
  | { tag: 0; h1: string } // TNode
  | { tag: 1; h1: string; h2: List<Attrib<Msg>>; h3: List<VNode<Msg>> };

type FancyElement<Msg> = Element & { events?: Record<string, Attrib<Msg> > };

// the pfunc will have two dummy arguments in front, and I dunno no node?
export function runapp<Model, Msg>(
  node: Node,
  init: Model,
  update: (_: Msg) => (_: Model) => Model,
  view: (_: Model) => VNode<Msg>,
) {
  function replace(parent: Node, node: Node | undefined, child: Node) {
    if (node) {
      parent.insertBefore(child, node);
      parent.removeChild(node);
    } else {
      parent.appendChild(child);
    }
    return child;
  }
  // patch node, possibly returning a new node
  function patch<Msg>(
    parentNode: Node,
    node: Node | undefined,
    vnode: VNode<Msg>,
  ): Node {
    if (vnode.tag == 0) {
      if (node && node.nodeType == 3) {
        node.nodeValue = vnode.h1;
        return node;
      }
      return replace(parentNode, node, document.createTextNode(vnode.h1));
    }
    let el: FancyElement<Msg>;
    if (node instanceof Element && node.tagName.toLowerCase() == vnode.h1) {
      el = node;
    } else {
      el = document.createElement(vnode.h1);
    }
    // update node here
    let has: Record<string, boolean> = {};
    for (let attrs = vnode.h2; attrs.tag == 1; attrs = attrs.h2) {
      let attr = attrs.h1;
      if (attr.tag == 0) {
        let key = attr.h1;
        has[key] = true;
        if (key in el)
          (el as any)[key] = attr.h2
        else
          el.setAttribute(key, attr.h2);
      } else {
        // onBlah
        let key = attr.h1.slice(2).toLowerCase();
        has[key] = true;
        let events = el.events || (el.events = {});
        if (!events[key]) el.addEventListener(key, listener);
        events[key] = attr;
      }
    }
    // remove attrs, not efficient..
    for (let i = 0; i < el.attributes.length; ) {
      let attr = el.attributes[i];
      if (!has[attr.name]) {
        el.removeAttribute(attr.name);
      } else {
        i++;
      }
    }
    if (el.events) {
      for (let key of Object.keys(el.events)) {
        if (!has[key]) delete el.events[key];
      }
    }
    let i = 0;
    for (let kids = vnode.h3; kids.tag == 1; kids = kids.h2) {
      patch(el, el.childNodes[i++], kids.h1);
    }
    while (el.childNodes[i]) el.removeChild(el.childNodes[i]);

    return node == el ? node : replace(parentNode, node, el);
  }
  let model = init;
  let vdom = view(model);
  let listener = (ev: Event) => {
    let target = ev.target as FancyElement<Msg>;
    if (!target.events) return;
    const attr = target.events[ev.type]
    let action
    if (attr.tag === 2) {
      // probably need to pass back the event
      // we'll want to deal with keypress, change, ...
      let action = attr.h2(ev.target!.value)
      model = update(action)(model);
    } else if (attr.tag === 1) {
      model = update(attr.h2)(model);
    }
    vdom = view(model);
    node = patch(node.parentNode!, node, vdom);
  };
  node = patch(node.parentNode!, node, vdom);
}
[{
	"resource": "/Users/dunham/prj/newt/src/Web/spruce.ts",
	"owner": "typescript",
	"code": "2349",
	"severity": 8,
	"message": "This expression is not callable.\n  Not all constituents of type '((_: string) => Msg) | (Msg & Function)' are callable.\n    Type 'Msg & Function' has no call signatures.",
	"source": "ts",
	"startLineNumber": 101,
	"startColumn": 16,
	"endLineNumber": 101,
	"endColumn": 19,
	"modelVersionId": 289,
	"origin": "extHost1"
}]
