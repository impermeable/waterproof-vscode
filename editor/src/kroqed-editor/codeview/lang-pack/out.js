"use strict";

// ../../../../../node_modules/@lezer/common/dist/index.js
var DefaultBufferLength = 1024;
var nextPropID = 0;
var Range = class {
  constructor(from, to) {
    this.from = from;
    this.to = to;
  }
};
var NodeProp = class {
  /**
  Create a new node prop type.
  */
  constructor(config = {}) {
    this.id = nextPropID++;
    this.perNode = !!config.perNode;
    this.deserialize = config.deserialize || (() => {
      throw new Error("This node type doesn't define a deserialize function");
    });
  }
  /**
  This is meant to be used with
  [`NodeSet.extend`](#common.NodeSet.extend) or
  [`LRParser.configure`](#lr.ParserConfig.props) to compute
  prop values for each node type in the set. Takes a [match
  object](#common.NodeType^match) or function that returns undefined
  if the node type doesn't get this prop, and the prop's value if
  it does.
  */
  add(match) {
    if (this.perNode)
      throw new RangeError("Can't add per-node props to node types");
    if (typeof match != "function")
      match = NodeType.match(match);
    return (type) => {
      let result = match(type);
      return result === void 0 ? null : [this, result];
    };
  }
};
NodeProp.closedBy = new NodeProp({ deserialize: (str) => str.split(" ") });
NodeProp.openedBy = new NodeProp({ deserialize: (str) => str.split(" ") });
NodeProp.group = new NodeProp({ deserialize: (str) => str.split(" ") });
NodeProp.isolate = new NodeProp({ deserialize: (value) => {
  if (value && value != "rtl" && value != "ltr" && value != "auto")
    throw new RangeError("Invalid value for isolate: " + value);
  return value || "auto";
} });
NodeProp.contextHash = new NodeProp({ perNode: true });
NodeProp.lookAhead = new NodeProp({ perNode: true });
NodeProp.mounted = new NodeProp({ perNode: true });
var MountedTree = class {
  constructor(tree, overlay, parser2) {
    this.tree = tree;
    this.overlay = overlay;
    this.parser = parser2;
  }
  /**
  @internal
  */
  static get(tree) {
    return tree && tree.props && tree.props[NodeProp.mounted.id];
  }
};
var noProps = /* @__PURE__ */ Object.create(null);
var NodeType = class {
  /**
  @internal
  */
  constructor(name, props, id, flags = 0) {
    this.name = name;
    this.props = props;
    this.id = id;
    this.flags = flags;
  }
  /**
  Define a node type.
  */
  static define(spec) {
    let props = spec.props && spec.props.length ? /* @__PURE__ */ Object.create(null) : noProps;
    let flags = (spec.top ? 1 : 0) | (spec.skipped ? 2 : 0) | (spec.error ? 4 : 0) | (spec.name == null ? 8 : 0);
    let type = new NodeType(spec.name || "", props, spec.id, flags);
    if (spec.props)
      for (let src of spec.props) {
        if (!Array.isArray(src))
          src = src(type);
        if (src) {
          if (src[0].perNode)
            throw new RangeError("Can't store a per-node prop on a node type");
          props[src[0].id] = src[1];
        }
      }
    return type;
  }
  /**
  Retrieves a node prop for this type. Will return `undefined` if
  the prop isn't present on this node.
  */
  prop(prop) {
    return this.props[prop.id];
  }
  /**
  True when this is the top node of a grammar.
  */
  get isTop() {
    return (this.flags & 1) > 0;
  }
  /**
  True when this node is produced by a skip rule.
  */
  get isSkipped() {
    return (this.flags & 2) > 0;
  }
  /**
  Indicates whether this is an error node.
  */
  get isError() {
    return (this.flags & 4) > 0;
  }
  /**
  When true, this node type doesn't correspond to a user-declared
  named node, for example because it is used to cache repetition.
  */
  get isAnonymous() {
    return (this.flags & 8) > 0;
  }
  /**
  Returns true when this node's name or one of its
  [groups](#common.NodeProp^group) matches the given string.
  */
  is(name) {
    if (typeof name == "string") {
      if (this.name == name)
        return true;
      let group = this.prop(NodeProp.group);
      return group ? group.indexOf(name) > -1 : false;
    }
    return this.id == name;
  }
  /**
  Create a function from node types to arbitrary values by
  specifying an object whose property names are node or
  [group](#common.NodeProp^group) names. Often useful with
  [`NodeProp.add`](#common.NodeProp.add). You can put multiple
  names, separated by spaces, in a single property name to map
  multiple node names to a single value.
  */
  static match(map) {
    let direct = /* @__PURE__ */ Object.create(null);
    for (let prop in map)
      for (let name of prop.split(" "))
        direct[name] = map[prop];
    return (node) => {
      for (let groups = node.prop(NodeProp.group), i = -1; i < (groups ? groups.length : 0); i++) {
        let found = direct[i < 0 ? node.name : groups[i]];
        if (found)
          return found;
      }
    };
  }
};
NodeType.none = new NodeType(
  "",
  /* @__PURE__ */ Object.create(null),
  0,
  8
  /* NodeFlag.Anonymous */
);
var NodeSet = class {
  /**
  Create a set with the given types. The `id` property of each
  type should correspond to its position within the array.
  */
  constructor(types) {
    this.types = types;
    for (let i = 0; i < types.length; i++)
      if (types[i].id != i)
        throw new RangeError("Node type ids should correspond to array positions when creating a node set");
  }
  /**
  Create a copy of this set with some node properties added. The
  arguments to this method can be created with
  [`NodeProp.add`](#common.NodeProp.add).
  */
  extend(...props) {
    let newTypes = [];
    for (let type of this.types) {
      let newProps = null;
      for (let source of props) {
        let add = source(type);
        if (add) {
          if (!newProps)
            newProps = Object.assign({}, type.props);
          newProps[add[0].id] = add[1];
        }
      }
      newTypes.push(newProps ? new NodeType(type.name, newProps, type.id, type.flags) : type);
    }
    return new NodeSet(newTypes);
  }
};
var CachedNode = /* @__PURE__ */ new WeakMap();
var CachedInnerNode = /* @__PURE__ */ new WeakMap();
var IterMode;
(function(IterMode2) {
  IterMode2[IterMode2["ExcludeBuffers"] = 1] = "ExcludeBuffers";
  IterMode2[IterMode2["IncludeAnonymous"] = 2] = "IncludeAnonymous";
  IterMode2[IterMode2["IgnoreMounts"] = 4] = "IgnoreMounts";
  IterMode2[IterMode2["IgnoreOverlays"] = 8] = "IgnoreOverlays";
})(IterMode || (IterMode = {}));
var Tree = class {
  /**
  Construct a new tree. See also [`Tree.build`](#common.Tree^build).
  */
  constructor(type, children, positions, length, props) {
    this.type = type;
    this.children = children;
    this.positions = positions;
    this.length = length;
    this.props = null;
    if (props && props.length) {
      this.props = /* @__PURE__ */ Object.create(null);
      for (let [prop, value] of props)
        this.props[typeof prop == "number" ? prop : prop.id] = value;
    }
  }
  /**
  @internal
  */
  toString() {
    let mounted = MountedTree.get(this);
    if (mounted && !mounted.overlay)
      return mounted.tree.toString();
    let children = "";
    for (let ch of this.children) {
      let str = ch.toString();
      if (str) {
        if (children)
          children += ",";
        children += str;
      }
    }
    return !this.type.name ? children : (/\W/.test(this.type.name) && !this.type.isError ? JSON.stringify(this.type.name) : this.type.name) + (children.length ? "(" + children + ")" : "");
  }
  /**
  Get a [tree cursor](#common.TreeCursor) positioned at the top of
  the tree. Mode can be used to [control](#common.IterMode) which
  nodes the cursor visits.
  */
  cursor(mode = 0) {
    return new TreeCursor(this.topNode, mode);
  }
  /**
  Get a [tree cursor](#common.TreeCursor) pointing into this tree
  at the given position and side (see
  [`moveTo`](#common.TreeCursor.moveTo).
  */
  cursorAt(pos, side = 0, mode = 0) {
    let scope = CachedNode.get(this) || this.topNode;
    let cursor = new TreeCursor(scope);
    cursor.moveTo(pos, side);
    CachedNode.set(this, cursor._tree);
    return cursor;
  }
  /**
  Get a [syntax node](#common.SyntaxNode) object for the top of the
  tree.
  */
  get topNode() {
    return new TreeNode(this, 0, 0, null);
  }
  /**
  Get the [syntax node](#common.SyntaxNode) at the given position.
  If `side` is -1, this will move into nodes that end at the
  position. If 1, it'll move into nodes that start at the
  position. With 0, it'll only enter nodes that cover the position
  from both sides.
  
  Note that this will not enter
  [overlays](#common.MountedTree.overlay), and you often want
  [`resolveInner`](#common.Tree.resolveInner) instead.
  */
  resolve(pos, side = 0) {
    let node = resolveNode(CachedNode.get(this) || this.topNode, pos, side, false);
    CachedNode.set(this, node);
    return node;
  }
  /**
  Like [`resolve`](#common.Tree.resolve), but will enter
  [overlaid](#common.MountedTree.overlay) nodes, producing a syntax node
  pointing into the innermost overlaid tree at the given position
  (with parent links going through all parent structure, including
  the host trees).
  */
  resolveInner(pos, side = 0) {
    let node = resolveNode(CachedInnerNode.get(this) || this.topNode, pos, side, true);
    CachedInnerNode.set(this, node);
    return node;
  }
  /**
  In some situations, it can be useful to iterate through all
  nodes around a position, including those in overlays that don't
  directly cover the position. This method gives you an iterator
  that will produce all nodes, from small to big, around the given
  position.
  */
  resolveStack(pos, side = 0) {
    return stackIterator(this, pos, side);
  }
  /**
  Iterate over the tree and its children, calling `enter` for any
  node that touches the `from`/`to` region (if given) before
  running over such a node's children, and `leave` (if given) when
  leaving the node. When `enter` returns `false`, that node will
  not have its children iterated over (or `leave` called).
  */
  iterate(spec) {
    let { enter, leave, from = 0, to = this.length } = spec;
    let mode = spec.mode || 0, anon = (mode & IterMode.IncludeAnonymous) > 0;
    for (let c = this.cursor(mode | IterMode.IncludeAnonymous); ; ) {
      let entered = false;
      if (c.from <= to && c.to >= from && (!anon && c.type.isAnonymous || enter(c) !== false)) {
        if (c.firstChild())
          continue;
        entered = true;
      }
      for (; ; ) {
        if (entered && leave && (anon || !c.type.isAnonymous))
          leave(c);
        if (c.nextSibling())
          break;
        if (!c.parent())
          return;
        entered = true;
      }
    }
  }
  /**
  Get the value of the given [node prop](#common.NodeProp) for this
  node. Works with both per-node and per-type props.
  */
  prop(prop) {
    return !prop.perNode ? this.type.prop(prop) : this.props ? this.props[prop.id] : void 0;
  }
  /**
  Returns the node's [per-node props](#common.NodeProp.perNode) in a
  format that can be passed to the [`Tree`](#common.Tree)
  constructor.
  */
  get propValues() {
    let result = [];
    if (this.props)
      for (let id in this.props)
        result.push([+id, this.props[id]]);
    return result;
  }
  /**
  Balance the direct children of this tree, producing a copy of
  which may have children grouped into subtrees with type
  [`NodeType.none`](#common.NodeType^none).
  */
  balance(config = {}) {
    return this.children.length <= 8 ? this : balanceRange(NodeType.none, this.children, this.positions, 0, this.children.length, 0, this.length, (children, positions, length) => new Tree(this.type, children, positions, length, this.propValues), config.makeTree || ((children, positions, length) => new Tree(NodeType.none, children, positions, length)));
  }
  /**
  Build a tree from a postfix-ordered buffer of node information,
  or a cursor over such a buffer.
  */
  static build(data) {
    return buildTree(data);
  }
};
Tree.empty = new Tree(NodeType.none, [], [], 0);
var FlatBufferCursor = class {
  constructor(buffer, index) {
    this.buffer = buffer;
    this.index = index;
  }
  get id() {
    return this.buffer[this.index - 4];
  }
  get start() {
    return this.buffer[this.index - 3];
  }
  get end() {
    return this.buffer[this.index - 2];
  }
  get size() {
    return this.buffer[this.index - 1];
  }
  get pos() {
    return this.index;
  }
  next() {
    this.index -= 4;
  }
  fork() {
    return new FlatBufferCursor(this.buffer, this.index);
  }
};
var TreeBuffer = class {
  /**
  Create a tree buffer.
  */
  constructor(buffer, length, set) {
    this.buffer = buffer;
    this.length = length;
    this.set = set;
  }
  /**
  @internal
  */
  get type() {
    return NodeType.none;
  }
  /**
  @internal
  */
  toString() {
    let result = [];
    for (let index = 0; index < this.buffer.length; ) {
      result.push(this.childString(index));
      index = this.buffer[index + 3];
    }
    return result.join(",");
  }
  /**
  @internal
  */
  childString(index) {
    let id = this.buffer[index], endIndex = this.buffer[index + 3];
    let type = this.set.types[id], result = type.name;
    if (/\W/.test(result) && !type.isError)
      result = JSON.stringify(result);
    index += 4;
    if (endIndex == index)
      return result;
    let children = [];
    while (index < endIndex) {
      children.push(this.childString(index));
      index = this.buffer[index + 3];
    }
    return result + "(" + children.join(",") + ")";
  }
  /**
  @internal
  */
  findChild(startIndex, endIndex, dir, pos, side) {
    let { buffer } = this, pick = -1;
    for (let i = startIndex; i != endIndex; i = buffer[i + 3]) {
      if (checkSide(side, pos, buffer[i + 1], buffer[i + 2])) {
        pick = i;
        if (dir > 0)
          break;
      }
    }
    return pick;
  }
  /**
  @internal
  */
  slice(startI, endI, from) {
    let b = this.buffer;
    let copy = new Uint16Array(endI - startI), len = 0;
    for (let i = startI, j = 0; i < endI; ) {
      copy[j++] = b[i++];
      copy[j++] = b[i++] - from;
      let to = copy[j++] = b[i++] - from;
      copy[j++] = b[i++] - startI;
      len = Math.max(len, to);
    }
    return new TreeBuffer(copy, len, this.set);
  }
};
function checkSide(side, pos, from, to) {
  switch (side) {
    case -2:
      return from < pos;
    case -1:
      return to >= pos && from < pos;
    case 0:
      return from < pos && to > pos;
    case 1:
      return from <= pos && to > pos;
    case 2:
      return to > pos;
    case 4:
      return true;
  }
}
function resolveNode(node, pos, side, overlays) {
  var _a;
  while (node.from == node.to || (side < 1 ? node.from >= pos : node.from > pos) || (side > -1 ? node.to <= pos : node.to < pos)) {
    let parent = !overlays && node instanceof TreeNode && node.index < 0 ? null : node.parent;
    if (!parent)
      return node;
    node = parent;
  }
  let mode = overlays ? 0 : IterMode.IgnoreOverlays;
  if (overlays)
    for (let scan = node, parent = scan.parent; parent; scan = parent, parent = scan.parent) {
      if (scan instanceof TreeNode && scan.index < 0 && ((_a = parent.enter(pos, side, mode)) === null || _a === void 0 ? void 0 : _a.from) != scan.from)
        node = parent;
    }
  for (; ; ) {
    let inner = node.enter(pos, side, mode);
    if (!inner)
      return node;
    node = inner;
  }
}
var BaseNode = class {
  cursor(mode = 0) {
    return new TreeCursor(this, mode);
  }
  getChild(type, before = null, after = null) {
    let r = getChildren(this, type, before, after);
    return r.length ? r[0] : null;
  }
  getChildren(type, before = null, after = null) {
    return getChildren(this, type, before, after);
  }
  resolve(pos, side = 0) {
    return resolveNode(this, pos, side, false);
  }
  resolveInner(pos, side = 0) {
    return resolveNode(this, pos, side, true);
  }
  matchContext(context) {
    return matchNodeContext(this.parent, context);
  }
  enterUnfinishedNodesBefore(pos) {
    let scan = this.childBefore(pos), node = this;
    while (scan) {
      let last = scan.lastChild;
      if (!last || last.to != scan.to)
        break;
      if (last.type.isError && last.from == last.to) {
        node = scan;
        scan = last.prevSibling;
      } else {
        scan = last;
      }
    }
    return node;
  }
  get node() {
    return this;
  }
  get next() {
    return this.parent;
  }
};
var TreeNode = class extends BaseNode {
  constructor(_tree, from, index, _parent) {
    super();
    this._tree = _tree;
    this.from = from;
    this.index = index;
    this._parent = _parent;
  }
  get type() {
    return this._tree.type;
  }
  get name() {
    return this._tree.type.name;
  }
  get to() {
    return this.from + this._tree.length;
  }
  nextChild(i, dir, pos, side, mode = 0) {
    for (let parent = this; ; ) {
      for (let { children, positions } = parent._tree, e = dir > 0 ? children.length : -1; i != e; i += dir) {
        let next = children[i], start = positions[i] + parent.from;
        if (!checkSide(side, pos, start, start + next.length))
          continue;
        if (next instanceof TreeBuffer) {
          if (mode & IterMode.ExcludeBuffers)
            continue;
          let index = next.findChild(0, next.buffer.length, dir, pos - start, side);
          if (index > -1)
            return new BufferNode(new BufferContext(parent, next, i, start), null, index);
        } else if (mode & IterMode.IncludeAnonymous || (!next.type.isAnonymous || hasChild(next))) {
          let mounted;
          if (!(mode & IterMode.IgnoreMounts) && (mounted = MountedTree.get(next)) && !mounted.overlay)
            return new TreeNode(mounted.tree, start, i, parent);
          let inner = new TreeNode(next, start, i, parent);
          return mode & IterMode.IncludeAnonymous || !inner.type.isAnonymous ? inner : inner.nextChild(dir < 0 ? next.children.length - 1 : 0, dir, pos, side);
        }
      }
      if (mode & IterMode.IncludeAnonymous || !parent.type.isAnonymous)
        return null;
      if (parent.index >= 0)
        i = parent.index + dir;
      else
        i = dir < 0 ? -1 : parent._parent._tree.children.length;
      parent = parent._parent;
      if (!parent)
        return null;
    }
  }
  get firstChild() {
    return this.nextChild(
      0,
      1,
      0,
      4
      /* Side.DontCare */
    );
  }
  get lastChild() {
    return this.nextChild(
      this._tree.children.length - 1,
      -1,
      0,
      4
      /* Side.DontCare */
    );
  }
  childAfter(pos) {
    return this.nextChild(
      0,
      1,
      pos,
      2
      /* Side.After */
    );
  }
  childBefore(pos) {
    return this.nextChild(
      this._tree.children.length - 1,
      -1,
      pos,
      -2
      /* Side.Before */
    );
  }
  enter(pos, side, mode = 0) {
    let mounted;
    if (!(mode & IterMode.IgnoreOverlays) && (mounted = MountedTree.get(this._tree)) && mounted.overlay) {
      let rPos = pos - this.from;
      for (let { from, to } of mounted.overlay) {
        if ((side > 0 ? from <= rPos : from < rPos) && (side < 0 ? to >= rPos : to > rPos))
          return new TreeNode(mounted.tree, mounted.overlay[0].from + this.from, -1, this);
      }
    }
    return this.nextChild(0, 1, pos, side, mode);
  }
  nextSignificantParent() {
    let val = this;
    while (val.type.isAnonymous && val._parent)
      val = val._parent;
    return val;
  }
  get parent() {
    return this._parent ? this._parent.nextSignificantParent() : null;
  }
  get nextSibling() {
    return this._parent && this.index >= 0 ? this._parent.nextChild(
      this.index + 1,
      1,
      0,
      4
      /* Side.DontCare */
    ) : null;
  }
  get prevSibling() {
    return this._parent && this.index >= 0 ? this._parent.nextChild(
      this.index - 1,
      -1,
      0,
      4
      /* Side.DontCare */
    ) : null;
  }
  get tree() {
    return this._tree;
  }
  toTree() {
    return this._tree;
  }
  /**
  @internal
  */
  toString() {
    return this._tree.toString();
  }
};
function getChildren(node, type, before, after) {
  let cur = node.cursor(), result = [];
  if (!cur.firstChild())
    return result;
  if (before != null)
    for (let found = false; !found; ) {
      found = cur.type.is(before);
      if (!cur.nextSibling())
        return result;
    }
  for (; ; ) {
    if (after != null && cur.type.is(after))
      return result;
    if (cur.type.is(type))
      result.push(cur.node);
    if (!cur.nextSibling())
      return after == null ? result : [];
  }
}
function matchNodeContext(node, context, i = context.length - 1) {
  for (let p = node; i >= 0; p = p.parent) {
    if (!p)
      return false;
    if (!p.type.isAnonymous) {
      if (context[i] && context[i] != p.name)
        return false;
      i--;
    }
  }
  return true;
}
var BufferContext = class {
  constructor(parent, buffer, index, start) {
    this.parent = parent;
    this.buffer = buffer;
    this.index = index;
    this.start = start;
  }
};
var BufferNode = class extends BaseNode {
  get name() {
    return this.type.name;
  }
  get from() {
    return this.context.start + this.context.buffer.buffer[this.index + 1];
  }
  get to() {
    return this.context.start + this.context.buffer.buffer[this.index + 2];
  }
  constructor(context, _parent, index) {
    super();
    this.context = context;
    this._parent = _parent;
    this.index = index;
    this.type = context.buffer.set.types[context.buffer.buffer[index]];
  }
  child(dir, pos, side) {
    let { buffer } = this.context;
    let index = buffer.findChild(this.index + 4, buffer.buffer[this.index + 3], dir, pos - this.context.start, side);
    return index < 0 ? null : new BufferNode(this.context, this, index);
  }
  get firstChild() {
    return this.child(
      1,
      0,
      4
      /* Side.DontCare */
    );
  }
  get lastChild() {
    return this.child(
      -1,
      0,
      4
      /* Side.DontCare */
    );
  }
  childAfter(pos) {
    return this.child(
      1,
      pos,
      2
      /* Side.After */
    );
  }
  childBefore(pos) {
    return this.child(
      -1,
      pos,
      -2
      /* Side.Before */
    );
  }
  enter(pos, side, mode = 0) {
    if (mode & IterMode.ExcludeBuffers)
      return null;
    let { buffer } = this.context;
    let index = buffer.findChild(this.index + 4, buffer.buffer[this.index + 3], side > 0 ? 1 : -1, pos - this.context.start, side);
    return index < 0 ? null : new BufferNode(this.context, this, index);
  }
  get parent() {
    return this._parent || this.context.parent.nextSignificantParent();
  }
  externalSibling(dir) {
    return this._parent ? null : this.context.parent.nextChild(
      this.context.index + dir,
      dir,
      0,
      4
      /* Side.DontCare */
    );
  }
  get nextSibling() {
    let { buffer } = this.context;
    let after = buffer.buffer[this.index + 3];
    if (after < (this._parent ? buffer.buffer[this._parent.index + 3] : buffer.buffer.length))
      return new BufferNode(this.context, this._parent, after);
    return this.externalSibling(1);
  }
  get prevSibling() {
    let { buffer } = this.context;
    let parentStart = this._parent ? this._parent.index + 4 : 0;
    if (this.index == parentStart)
      return this.externalSibling(-1);
    return new BufferNode(this.context, this._parent, buffer.findChild(
      parentStart,
      this.index,
      -1,
      0,
      4
      /* Side.DontCare */
    ));
  }
  get tree() {
    return null;
  }
  toTree() {
    let children = [], positions = [];
    let { buffer } = this.context;
    let startI = this.index + 4, endI = buffer.buffer[this.index + 3];
    if (endI > startI) {
      let from = buffer.buffer[this.index + 1];
      children.push(buffer.slice(startI, endI, from));
      positions.push(0);
    }
    return new Tree(this.type, children, positions, this.to - this.from);
  }
  /**
  @internal
  */
  toString() {
    return this.context.buffer.childString(this.index);
  }
};
function iterStack(heads) {
  if (!heads.length)
    return null;
  let pick = 0, picked = heads[0];
  for (let i = 1; i < heads.length; i++) {
    let node = heads[i];
    if (node.from > picked.from || node.to < picked.to) {
      picked = node;
      pick = i;
    }
  }
  let next = picked instanceof TreeNode && picked.index < 0 ? null : picked.parent;
  let newHeads = heads.slice();
  if (next)
    newHeads[pick] = next;
  else
    newHeads.splice(pick, 1);
  return new StackIterator(newHeads, picked);
}
var StackIterator = class {
  constructor(heads, node) {
    this.heads = heads;
    this.node = node;
  }
  get next() {
    return iterStack(this.heads);
  }
};
function stackIterator(tree, pos, side) {
  let inner = tree.resolveInner(pos, side), layers = null;
  for (let scan = inner instanceof TreeNode ? inner : inner.context.parent; scan; scan = scan.parent) {
    if (scan.index < 0) {
      let parent = scan.parent;
      (layers || (layers = [inner])).push(parent.resolve(pos, side));
      scan = parent;
    } else {
      let mount = MountedTree.get(scan.tree);
      if (mount && mount.overlay && mount.overlay[0].from <= pos && mount.overlay[mount.overlay.length - 1].to >= pos) {
        let root = new TreeNode(mount.tree, mount.overlay[0].from + scan.from, -1, scan);
        (layers || (layers = [inner])).push(resolveNode(root, pos, side, false));
      }
    }
  }
  return layers ? iterStack(layers) : inner;
}
var TreeCursor = class {
  /**
  Shorthand for `.type.name`.
  */
  get name() {
    return this.type.name;
  }
  /**
  @internal
  */
  constructor(node, mode = 0) {
    this.mode = mode;
    this.buffer = null;
    this.stack = [];
    this.index = 0;
    this.bufferNode = null;
    if (node instanceof TreeNode) {
      this.yieldNode(node);
    } else {
      this._tree = node.context.parent;
      this.buffer = node.context;
      for (let n = node._parent; n; n = n._parent)
        this.stack.unshift(n.index);
      this.bufferNode = node;
      this.yieldBuf(node.index);
    }
  }
  yieldNode(node) {
    if (!node)
      return false;
    this._tree = node;
    this.type = node.type;
    this.from = node.from;
    this.to = node.to;
    return true;
  }
  yieldBuf(index, type) {
    this.index = index;
    let { start, buffer } = this.buffer;
    this.type = type || buffer.set.types[buffer.buffer[index]];
    this.from = start + buffer.buffer[index + 1];
    this.to = start + buffer.buffer[index + 2];
    return true;
  }
  /**
  @internal
  */
  yield(node) {
    if (!node)
      return false;
    if (node instanceof TreeNode) {
      this.buffer = null;
      return this.yieldNode(node);
    }
    this.buffer = node.context;
    return this.yieldBuf(node.index, node.type);
  }
  /**
  @internal
  */
  toString() {
    return this.buffer ? this.buffer.buffer.childString(this.index) : this._tree.toString();
  }
  /**
  @internal
  */
  enterChild(dir, pos, side) {
    if (!this.buffer)
      return this.yield(this._tree.nextChild(dir < 0 ? this._tree._tree.children.length - 1 : 0, dir, pos, side, this.mode));
    let { buffer } = this.buffer;
    let index = buffer.findChild(this.index + 4, buffer.buffer[this.index + 3], dir, pos - this.buffer.start, side);
    if (index < 0)
      return false;
    this.stack.push(this.index);
    return this.yieldBuf(index);
  }
  /**
  Move the cursor to this node's first child. When this returns
  false, the node has no child, and the cursor has not been moved.
  */
  firstChild() {
    return this.enterChild(
      1,
      0,
      4
      /* Side.DontCare */
    );
  }
  /**
  Move the cursor to this node's last child.
  */
  lastChild() {
    return this.enterChild(
      -1,
      0,
      4
      /* Side.DontCare */
    );
  }
  /**
  Move the cursor to the first child that ends after `pos`.
  */
  childAfter(pos) {
    return this.enterChild(
      1,
      pos,
      2
      /* Side.After */
    );
  }
  /**
  Move to the last child that starts before `pos`.
  */
  childBefore(pos) {
    return this.enterChild(
      -1,
      pos,
      -2
      /* Side.Before */
    );
  }
  /**
  Move the cursor to the child around `pos`. If side is -1 the
  child may end at that position, when 1 it may start there. This
  will also enter [overlaid](#common.MountedTree.overlay)
  [mounted](#common.NodeProp^mounted) trees unless `overlays` is
  set to false.
  */
  enter(pos, side, mode = this.mode) {
    if (!this.buffer)
      return this.yield(this._tree.enter(pos, side, mode));
    return mode & IterMode.ExcludeBuffers ? false : this.enterChild(1, pos, side);
  }
  /**
  Move to the node's parent node, if this isn't the top node.
  */
  parent() {
    if (!this.buffer)
      return this.yieldNode(this.mode & IterMode.IncludeAnonymous ? this._tree._parent : this._tree.parent);
    if (this.stack.length)
      return this.yieldBuf(this.stack.pop());
    let parent = this.mode & IterMode.IncludeAnonymous ? this.buffer.parent : this.buffer.parent.nextSignificantParent();
    this.buffer = null;
    return this.yieldNode(parent);
  }
  /**
  @internal
  */
  sibling(dir) {
    if (!this.buffer)
      return !this._tree._parent ? false : this.yield(this._tree.index < 0 ? null : this._tree._parent.nextChild(this._tree.index + dir, dir, 0, 4, this.mode));
    let { buffer } = this.buffer, d = this.stack.length - 1;
    if (dir < 0) {
      let parentStart = d < 0 ? 0 : this.stack[d] + 4;
      if (this.index != parentStart)
        return this.yieldBuf(buffer.findChild(
          parentStart,
          this.index,
          -1,
          0,
          4
          /* Side.DontCare */
        ));
    } else {
      let after = buffer.buffer[this.index + 3];
      if (after < (d < 0 ? buffer.buffer.length : buffer.buffer[this.stack[d] + 3]))
        return this.yieldBuf(after);
    }
    return d < 0 ? this.yield(this.buffer.parent.nextChild(this.buffer.index + dir, dir, 0, 4, this.mode)) : false;
  }
  /**
  Move to this node's next sibling, if any.
  */
  nextSibling() {
    return this.sibling(1);
  }
  /**
  Move to this node's previous sibling, if any.
  */
  prevSibling() {
    return this.sibling(-1);
  }
  atLastNode(dir) {
    let index, parent, { buffer } = this;
    if (buffer) {
      if (dir > 0) {
        if (this.index < buffer.buffer.buffer.length)
          return false;
      } else {
        for (let i = 0; i < this.index; i++)
          if (buffer.buffer.buffer[i + 3] < this.index)
            return false;
      }
      ({ index, parent } = buffer);
    } else {
      ({ index, _parent: parent } = this._tree);
    }
    for (; parent; { index, _parent: parent } = parent) {
      if (index > -1)
        for (let i = index + dir, e = dir < 0 ? -1 : parent._tree.children.length; i != e; i += dir) {
          let child = parent._tree.children[i];
          if (this.mode & IterMode.IncludeAnonymous || child instanceof TreeBuffer || !child.type.isAnonymous || hasChild(child))
            return false;
        }
    }
    return true;
  }
  move(dir, enter) {
    if (enter && this.enterChild(
      dir,
      0,
      4
      /* Side.DontCare */
    ))
      return true;
    for (; ; ) {
      if (this.sibling(dir))
        return true;
      if (this.atLastNode(dir) || !this.parent())
        return false;
    }
  }
  /**
  Move to the next node in a
  [pre-order](https://en.wikipedia.org/wiki/Tree_traversal#Pre-order,_NLR)
  traversal, going from a node to its first child or, if the
  current node is empty or `enter` is false, its next sibling or
  the next sibling of the first parent node that has one.
  */
  next(enter = true) {
    return this.move(1, enter);
  }
  /**
  Move to the next node in a last-to-first pre-order traversal. A
  node is followed by its last child or, if it has none, its
  previous sibling or the previous sibling of the first parent
  node that has one.
  */
  prev(enter = true) {
    return this.move(-1, enter);
  }
  /**
  Move the cursor to the innermost node that covers `pos`. If
  `side` is -1, it will enter nodes that end at `pos`. If it is 1,
  it will enter nodes that start at `pos`.
  */
  moveTo(pos, side = 0) {
    while (this.from == this.to || (side < 1 ? this.from >= pos : this.from > pos) || (side > -1 ? this.to <= pos : this.to < pos))
      if (!this.parent())
        break;
    while (this.enterChild(1, pos, side)) {
    }
    return this;
  }
  /**
  Get a [syntax node](#common.SyntaxNode) at the cursor's current
  position.
  */
  get node() {
    if (!this.buffer)
      return this._tree;
    let cache = this.bufferNode, result = null, depth = 0;
    if (cache && cache.context == this.buffer) {
      scan:
        for (let index = this.index, d = this.stack.length; d >= 0; ) {
          for (let c = cache; c; c = c._parent)
            if (c.index == index) {
              if (index == this.index)
                return c;
              result = c;
              depth = d + 1;
              break scan;
            }
          index = this.stack[--d];
        }
    }
    for (let i = depth; i < this.stack.length; i++)
      result = new BufferNode(this.buffer, result, this.stack[i]);
    return this.bufferNode = new BufferNode(this.buffer, result, this.index);
  }
  /**
  Get the [tree](#common.Tree) that represents the current node, if
  any. Will return null when the node is in a [tree
  buffer](#common.TreeBuffer).
  */
  get tree() {
    return this.buffer ? null : this._tree._tree;
  }
  /**
  Iterate over the current node and all its descendants, calling
  `enter` when entering a node and `leave`, if given, when leaving
  one. When `enter` returns `false`, any children of that node are
  skipped, and `leave` isn't called for it.
  */
  iterate(enter, leave) {
    for (let depth = 0; ; ) {
      let mustLeave = false;
      if (this.type.isAnonymous || enter(this) !== false) {
        if (this.firstChild()) {
          depth++;
          continue;
        }
        if (!this.type.isAnonymous)
          mustLeave = true;
      }
      for (; ; ) {
        if (mustLeave && leave)
          leave(this);
        mustLeave = this.type.isAnonymous;
        if (!depth)
          return;
        if (this.nextSibling())
          break;
        this.parent();
        depth--;
        mustLeave = true;
      }
    }
  }
  /**
  Test whether the current node matches a given context—a sequence
  of direct parent node names. Empty strings in the context array
  are treated as wildcards.
  */
  matchContext(context) {
    if (!this.buffer)
      return matchNodeContext(this.node.parent, context);
    let { buffer } = this.buffer, { types } = buffer.set;
    for (let i = context.length - 1, d = this.stack.length - 1; i >= 0; d--) {
      if (d < 0)
        return matchNodeContext(this._tree, context, i);
      let type = types[buffer.buffer[this.stack[d]]];
      if (!type.isAnonymous) {
        if (context[i] && context[i] != type.name)
          return false;
        i--;
      }
    }
    return true;
  }
};
function hasChild(tree) {
  return tree.children.some((ch) => ch instanceof TreeBuffer || !ch.type.isAnonymous || hasChild(ch));
}
function buildTree(data) {
  var _a;
  let { buffer, nodeSet, maxBufferLength = DefaultBufferLength, reused = [], minRepeatType = nodeSet.types.length } = data;
  let cursor = Array.isArray(buffer) ? new FlatBufferCursor(buffer, buffer.length) : buffer;
  let types = nodeSet.types;
  let contextHash = 0, lookAhead = 0;
  function takeNode(parentStart, minPos, children2, positions2, inRepeat, depth) {
    let { id, start, end, size } = cursor;
    let lookAheadAtStart = lookAhead, contextAtStart = contextHash;
    while (size < 0) {
      cursor.next();
      if (size == -1) {
        let node2 = reused[id];
        children2.push(node2);
        positions2.push(start - parentStart);
        return;
      } else if (size == -3) {
        contextHash = id;
        return;
      } else if (size == -4) {
        lookAhead = id;
        return;
      } else {
        throw new RangeError(`Unrecognized record size: ${size}`);
      }
    }
    let type = types[id], node, buffer2;
    let startPos = start - parentStart;
    if (end - start <= maxBufferLength && (buffer2 = findBufferSize(cursor.pos - minPos, inRepeat))) {
      let data2 = new Uint16Array(buffer2.size - buffer2.skip);
      let endPos = cursor.pos - buffer2.size, index = data2.length;
      while (cursor.pos > endPos)
        index = copyToBuffer(buffer2.start, data2, index);
      node = new TreeBuffer(data2, end - buffer2.start, nodeSet);
      startPos = buffer2.start - parentStart;
    } else {
      let endPos = cursor.pos - size;
      cursor.next();
      let localChildren = [], localPositions = [];
      let localInRepeat = id >= minRepeatType ? id : -1;
      let lastGroup = 0, lastEnd = end;
      while (cursor.pos > endPos) {
        if (localInRepeat >= 0 && cursor.id == localInRepeat && cursor.size >= 0) {
          if (cursor.end <= lastEnd - maxBufferLength) {
            makeRepeatLeaf(localChildren, localPositions, start, lastGroup, cursor.end, lastEnd, localInRepeat, lookAheadAtStart, contextAtStart);
            lastGroup = localChildren.length;
            lastEnd = cursor.end;
          }
          cursor.next();
        } else if (depth > 2500) {
          takeFlatNode(start, endPos, localChildren, localPositions);
        } else {
          takeNode(start, endPos, localChildren, localPositions, localInRepeat, depth + 1);
        }
      }
      if (localInRepeat >= 0 && lastGroup > 0 && lastGroup < localChildren.length)
        makeRepeatLeaf(localChildren, localPositions, start, lastGroup, start, lastEnd, localInRepeat, lookAheadAtStart, contextAtStart);
      localChildren.reverse();
      localPositions.reverse();
      if (localInRepeat > -1 && lastGroup > 0) {
        let make = makeBalanced(type, contextAtStart);
        node = balanceRange(type, localChildren, localPositions, 0, localChildren.length, 0, end - start, make, make);
      } else {
        node = makeTree(type, localChildren, localPositions, end - start, lookAheadAtStart - end, contextAtStart);
      }
    }
    children2.push(node);
    positions2.push(startPos);
  }
  function takeFlatNode(parentStart, minPos, children2, positions2) {
    let nodes = [];
    let nodeCount = 0, stopAt = -1;
    while (cursor.pos > minPos) {
      let { id, start, end, size } = cursor;
      if (size > 4) {
        cursor.next();
      } else if (stopAt > -1 && start < stopAt) {
        break;
      } else {
        if (stopAt < 0)
          stopAt = end - maxBufferLength;
        nodes.push(id, start, end);
        nodeCount++;
        cursor.next();
      }
    }
    if (nodeCount) {
      let buffer2 = new Uint16Array(nodeCount * 4);
      let start = nodes[nodes.length - 2];
      for (let i = nodes.length - 3, j = 0; i >= 0; i -= 3) {
        buffer2[j++] = nodes[i];
        buffer2[j++] = nodes[i + 1] - start;
        buffer2[j++] = nodes[i + 2] - start;
        buffer2[j++] = j;
      }
      children2.push(new TreeBuffer(buffer2, nodes[2] - start, nodeSet));
      positions2.push(start - parentStart);
    }
  }
  function makeBalanced(type, contextHash2) {
    return (children2, positions2, length2) => {
      let lookAhead2 = 0, lastI = children2.length - 1, last, lookAheadProp;
      if (lastI >= 0 && (last = children2[lastI]) instanceof Tree) {
        if (!lastI && last.type == type && last.length == length2)
          return last;
        if (lookAheadProp = last.prop(NodeProp.lookAhead))
          lookAhead2 = positions2[lastI] + last.length + lookAheadProp;
      }
      return makeTree(type, children2, positions2, length2, lookAhead2, contextHash2);
    };
  }
  function makeRepeatLeaf(children2, positions2, base, i, from, to, type, lookAhead2, contextHash2) {
    let localChildren = [], localPositions = [];
    while (children2.length > i) {
      localChildren.push(children2.pop());
      localPositions.push(positions2.pop() + base - from);
    }
    children2.push(makeTree(nodeSet.types[type], localChildren, localPositions, to - from, lookAhead2 - to, contextHash2));
    positions2.push(from - base);
  }
  function makeTree(type, children2, positions2, length2, lookAhead2, contextHash2, props) {
    if (contextHash2) {
      let pair2 = [NodeProp.contextHash, contextHash2];
      props = props ? [pair2].concat(props) : [pair2];
    }
    if (lookAhead2 > 25) {
      let pair2 = [NodeProp.lookAhead, lookAhead2];
      props = props ? [pair2].concat(props) : [pair2];
    }
    return new Tree(type, children2, positions2, length2, props);
  }
  function findBufferSize(maxSize, inRepeat) {
    let fork = cursor.fork();
    let size = 0, start = 0, skip = 0, minStart = fork.end - maxBufferLength;
    let result = { size: 0, start: 0, skip: 0 };
    scan:
      for (let minPos = fork.pos - maxSize; fork.pos > minPos; ) {
        let nodeSize2 = fork.size;
        if (fork.id == inRepeat && nodeSize2 >= 0) {
          result.size = size;
          result.start = start;
          result.skip = skip;
          skip += 4;
          size += 4;
          fork.next();
          continue;
        }
        let startPos = fork.pos - nodeSize2;
        if (nodeSize2 < 0 || startPos < minPos || fork.start < minStart)
          break;
        let localSkipped = fork.id >= minRepeatType ? 4 : 0;
        let nodeStart = fork.start;
        fork.next();
        while (fork.pos > startPos) {
          if (fork.size < 0) {
            if (fork.size == -3)
              localSkipped += 4;
            else
              break scan;
          } else if (fork.id >= minRepeatType) {
            localSkipped += 4;
          }
          fork.next();
        }
        start = nodeStart;
        size += nodeSize2;
        skip += localSkipped;
      }
    if (inRepeat < 0 || size == maxSize) {
      result.size = size;
      result.start = start;
      result.skip = skip;
    }
    return result.size > 4 ? result : void 0;
  }
  function copyToBuffer(bufferStart, buffer2, index) {
    let { id, start, end, size } = cursor;
    cursor.next();
    if (size >= 0 && id < minRepeatType) {
      let startIndex = index;
      if (size > 4) {
        let endPos = cursor.pos - (size - 4);
        while (cursor.pos > endPos)
          index = copyToBuffer(bufferStart, buffer2, index);
      }
      buffer2[--index] = startIndex;
      buffer2[--index] = end - bufferStart;
      buffer2[--index] = start - bufferStart;
      buffer2[--index] = id;
    } else if (size == -3) {
      contextHash = id;
    } else if (size == -4) {
      lookAhead = id;
    }
    return index;
  }
  let children = [], positions = [];
  while (cursor.pos > 0)
    takeNode(data.start || 0, data.bufferStart || 0, children, positions, -1, 0);
  let length = (_a = data.length) !== null && _a !== void 0 ? _a : children.length ? positions[0] + children[0].length : 0;
  return new Tree(types[data.topID], children.reverse(), positions.reverse(), length);
}
var nodeSizeCache = /* @__PURE__ */ new WeakMap();
function nodeSize(balanceType, node) {
  if (!balanceType.isAnonymous || node instanceof TreeBuffer || node.type != balanceType)
    return 1;
  let size = nodeSizeCache.get(node);
  if (size == null) {
    size = 1;
    for (let child of node.children) {
      if (child.type != balanceType || !(child instanceof Tree)) {
        size = 1;
        break;
      }
      size += nodeSize(balanceType, child);
    }
    nodeSizeCache.set(node, size);
  }
  return size;
}
function balanceRange(balanceType, children, positions, from, to, start, length, mkTop, mkTree) {
  let total = 0;
  for (let i = from; i < to; i++)
    total += nodeSize(balanceType, children[i]);
  let maxChild = Math.ceil(
    total * 1.5 / 8
    /* Balance.BranchFactor */
  );
  let localChildren = [], localPositions = [];
  function divide(children2, positions2, from2, to2, offset) {
    for (let i = from2; i < to2; ) {
      let groupFrom = i, groupStart = positions2[i], groupSize = nodeSize(balanceType, children2[i]);
      i++;
      for (; i < to2; i++) {
        let nextSize = nodeSize(balanceType, children2[i]);
        if (groupSize + nextSize >= maxChild)
          break;
        groupSize += nextSize;
      }
      if (i == groupFrom + 1) {
        if (groupSize > maxChild) {
          let only = children2[groupFrom];
          divide(only.children, only.positions, 0, only.children.length, positions2[groupFrom] + offset);
          continue;
        }
        localChildren.push(children2[groupFrom]);
      } else {
        let length2 = positions2[i - 1] + children2[i - 1].length - groupStart;
        localChildren.push(balanceRange(balanceType, children2, positions2, groupFrom, i, groupStart, length2, null, mkTree));
      }
      localPositions.push(groupStart + offset - start);
    }
  }
  divide(children, positions, from, to, 0);
  return (mkTop || mkTree)(localChildren, localPositions, length);
}
var Parser = class {
  /**
  Start a parse, returning a [partial parse](#common.PartialParse)
  object. [`fragments`](#common.TreeFragment) can be passed in to
  make the parse incremental.
  
  By default, the entire input is parsed. You can pass `ranges`,
  which should be a sorted array of non-empty, non-overlapping
  ranges, to parse only those ranges. The tree returned in that
  case will start at `ranges[0].from`.
  */
  startParse(input, fragments, ranges) {
    if (typeof input == "string")
      input = new StringInput(input);
    ranges = !ranges ? [new Range(0, input.length)] : ranges.length ? ranges.map((r) => new Range(r.from, r.to)) : [new Range(0, 0)];
    return this.createParse(input, fragments || [], ranges);
  }
  /**
  Run a full parse, returning the resulting tree.
  */
  parse(input, fragments, ranges) {
    let parse = this.startParse(input, fragments, ranges);
    for (; ; ) {
      let done = parse.advance();
      if (done)
        return done;
    }
  }
};
var StringInput = class {
  constructor(string) {
    this.string = string;
  }
  get length() {
    return this.string.length;
  }
  chunk(from) {
    return this.string.slice(from);
  }
  get lineChunks() {
    return false;
  }
  read(from, to) {
    return this.string.slice(from, to);
  }
};
var stoppedInner = new NodeProp({ perNode: true });

// ../../../../../node_modules/@lezer/lr/dist/index.js
var Stack = class {
  /**
  @internal
  */
  constructor(p, stack, state, reducePos, pos, score, buffer, bufferBase, curContext, lookAhead = 0, parent) {
    this.p = p;
    this.stack = stack;
    this.state = state;
    this.reducePos = reducePos;
    this.pos = pos;
    this.score = score;
    this.buffer = buffer;
    this.bufferBase = bufferBase;
    this.curContext = curContext;
    this.lookAhead = lookAhead;
    this.parent = parent;
  }
  /**
  @internal
  */
  toString() {
    return `[${this.stack.filter((_, i) => i % 3 == 0).concat(this.state)}]@${this.pos}${this.score ? "!" + this.score : ""}`;
  }
  // Start an empty stack
  /**
  @internal
  */
  static start(p, state, pos = 0) {
    let cx = p.parser.context;
    return new Stack(p, [], state, pos, pos, 0, [], 0, cx ? new StackContext(cx, cx.start) : null, 0, null);
  }
  /**
  The stack's current [context](#lr.ContextTracker) value, if
  any. Its type will depend on the context tracker's type
  parameter, or it will be `null` if there is no context
  tracker.
  */
  get context() {
    return this.curContext ? this.curContext.context : null;
  }
  // Push a state onto the stack, tracking its start position as well
  // as the buffer base at that point.
  /**
  @internal
  */
  pushState(state, start) {
    this.stack.push(this.state, start, this.bufferBase + this.buffer.length);
    this.state = state;
  }
  // Apply a reduce action
  /**
  @internal
  */
  reduce(action) {
    var _a;
    let depth = action >> 19, type = action & 65535;
    let { parser: parser2 } = this.p;
    let lookaheadRecord = this.reducePos < this.pos - 25;
    if (lookaheadRecord)
      this.setLookAhead(this.pos);
    let dPrec = parser2.dynamicPrecedence(type);
    if (dPrec)
      this.score += dPrec;
    if (depth == 0) {
      this.pushState(parser2.getGoto(this.state, type, true), this.reducePos);
      if (type < parser2.minRepeatTerm)
        this.storeNode(type, this.reducePos, this.reducePos, lookaheadRecord ? 8 : 4, true);
      this.reduceContext(type, this.reducePos);
      return;
    }
    let base = this.stack.length - (depth - 1) * 3 - (action & 262144 ? 6 : 0);
    let start = base ? this.stack[base - 2] : this.p.ranges[0].from, size = this.reducePos - start;
    if (size >= 2e3 && !((_a = this.p.parser.nodeSet.types[type]) === null || _a === void 0 ? void 0 : _a.isAnonymous)) {
      if (start == this.p.lastBigReductionStart) {
        this.p.bigReductionCount++;
        this.p.lastBigReductionSize = size;
      } else if (this.p.lastBigReductionSize < size) {
        this.p.bigReductionCount = 1;
        this.p.lastBigReductionStart = start;
        this.p.lastBigReductionSize = size;
      }
    }
    let bufferBase = base ? this.stack[base - 1] : 0, count = this.bufferBase + this.buffer.length - bufferBase;
    if (type < parser2.minRepeatTerm || action & 131072) {
      let pos = parser2.stateFlag(
        this.state,
        1
        /* StateFlag.Skipped */
      ) ? this.pos : this.reducePos;
      this.storeNode(type, start, pos, count + 4, true);
    }
    if (action & 262144) {
      this.state = this.stack[base];
    } else {
      let baseStateID = this.stack[base - 3];
      this.state = parser2.getGoto(baseStateID, type, true);
    }
    while (this.stack.length > base)
      this.stack.pop();
    this.reduceContext(type, start);
  }
  // Shift a value into the buffer
  /**
  @internal
  */
  storeNode(term, start, end, size = 4, mustSink = false) {
    if (term == 0 && (!this.stack.length || this.stack[this.stack.length - 1] < this.buffer.length + this.bufferBase)) {
      let cur = this, top = this.buffer.length;
      if (top == 0 && cur.parent) {
        top = cur.bufferBase - cur.parent.bufferBase;
        cur = cur.parent;
      }
      if (top > 0 && cur.buffer[top - 4] == 0 && cur.buffer[top - 1] > -1) {
        if (start == end)
          return;
        if (cur.buffer[top - 2] >= start) {
          cur.buffer[top - 2] = end;
          return;
        }
      }
    }
    if (!mustSink || this.pos == end) {
      this.buffer.push(term, start, end, size);
    } else {
      let index = this.buffer.length;
      if (index > 0 && this.buffer[index - 4] != 0) {
        let mustMove = false;
        for (let scan = index; scan > 0 && this.buffer[scan - 2] > end; scan -= 4) {
          if (this.buffer[scan - 1] >= 0) {
            mustMove = true;
            break;
          }
        }
        if (mustMove)
          while (index > 0 && this.buffer[index - 2] > end) {
            this.buffer[index] = this.buffer[index - 4];
            this.buffer[index + 1] = this.buffer[index - 3];
            this.buffer[index + 2] = this.buffer[index - 2];
            this.buffer[index + 3] = this.buffer[index - 1];
            index -= 4;
            if (size > 4)
              size -= 4;
          }
      }
      this.buffer[index] = term;
      this.buffer[index + 1] = start;
      this.buffer[index + 2] = end;
      this.buffer[index + 3] = size;
    }
  }
  // Apply a shift action
  /**
  @internal
  */
  shift(action, type, start, end) {
    if (action & 131072) {
      this.pushState(action & 65535, this.pos);
    } else if ((action & 262144) == 0) {
      let nextState = action, { parser: parser2 } = this.p;
      if (end > this.pos || type <= parser2.maxNode) {
        this.pos = end;
        if (!parser2.stateFlag(
          nextState,
          1
          /* StateFlag.Skipped */
        ))
          this.reducePos = end;
      }
      this.pushState(nextState, start);
      this.shiftContext(type, start);
      if (type <= parser2.maxNode)
        this.buffer.push(type, start, end, 4);
    } else {
      this.pos = end;
      this.shiftContext(type, start);
      if (type <= this.p.parser.maxNode)
        this.buffer.push(type, start, end, 4);
    }
  }
  // Apply an action
  /**
  @internal
  */
  apply(action, next, nextStart, nextEnd) {
    if (action & 65536)
      this.reduce(action);
    else
      this.shift(action, next, nextStart, nextEnd);
  }
  // Add a prebuilt (reused) node into the buffer.
  /**
  @internal
  */
  useNode(value, next) {
    let index = this.p.reused.length - 1;
    if (index < 0 || this.p.reused[index] != value) {
      this.p.reused.push(value);
      index++;
    }
    let start = this.pos;
    this.reducePos = this.pos = start + value.length;
    this.pushState(next, start);
    this.buffer.push(
      index,
      start,
      this.reducePos,
      -1
      /* size == -1 means this is a reused value */
    );
    if (this.curContext)
      this.updateContext(this.curContext.tracker.reuse(this.curContext.context, value, this, this.p.stream.reset(this.pos - value.length)));
  }
  // Split the stack. Due to the buffer sharing and the fact
  // that `this.stack` tends to stay quite shallow, this isn't very
  // expensive.
  /**
  @internal
  */
  split() {
    let parent = this;
    let off = parent.buffer.length;
    while (off > 0 && parent.buffer[off - 2] > parent.reducePos)
      off -= 4;
    let buffer = parent.buffer.slice(off), base = parent.bufferBase + off;
    while (parent && base == parent.bufferBase)
      parent = parent.parent;
    return new Stack(this.p, this.stack.slice(), this.state, this.reducePos, this.pos, this.score, buffer, base, this.curContext, this.lookAhead, parent);
  }
  // Try to recover from an error by 'deleting' (ignoring) one token.
  /**
  @internal
  */
  recoverByDelete(next, nextEnd) {
    let isNode = next <= this.p.parser.maxNode;
    if (isNode)
      this.storeNode(next, this.pos, nextEnd, 4);
    this.storeNode(0, this.pos, nextEnd, isNode ? 8 : 4);
    this.pos = this.reducePos = nextEnd;
    this.score -= 190;
  }
  /**
  Check if the given term would be able to be shifted (optionally
  after some reductions) on this stack. This can be useful for
  external tokenizers that want to make sure they only provide a
  given token when it applies.
  */
  canShift(term) {
    for (let sim = new SimulatedStack(this); ; ) {
      let action = this.p.parser.stateSlot(
        sim.state,
        4
        /* ParseState.DefaultReduce */
      ) || this.p.parser.hasAction(sim.state, term);
      if (action == 0)
        return false;
      if ((action & 65536) == 0)
        return true;
      sim.reduce(action);
    }
  }
  // Apply up to Recover.MaxNext recovery actions that conceptually
  // inserts some missing token or rule.
  /**
  @internal
  */
  recoverByInsert(next) {
    if (this.stack.length >= 300)
      return [];
    let nextStates = this.p.parser.nextStates(this.state);
    if (nextStates.length > 4 << 1 || this.stack.length >= 120) {
      let best = [];
      for (let i = 0, s; i < nextStates.length; i += 2) {
        if ((s = nextStates[i + 1]) != this.state && this.p.parser.hasAction(s, next))
          best.push(nextStates[i], s);
      }
      if (this.stack.length < 120)
        for (let i = 0; best.length < 4 << 1 && i < nextStates.length; i += 2) {
          let s = nextStates[i + 1];
          if (!best.some((v, i2) => i2 & 1 && v == s))
            best.push(nextStates[i], s);
        }
      nextStates = best;
    }
    let result = [];
    for (let i = 0; i < nextStates.length && result.length < 4; i += 2) {
      let s = nextStates[i + 1];
      if (s == this.state)
        continue;
      let stack = this.split();
      stack.pushState(s, this.pos);
      stack.storeNode(0, stack.pos, stack.pos, 4, true);
      stack.shiftContext(nextStates[i], this.pos);
      stack.reducePos = this.pos;
      stack.score -= 200;
      result.push(stack);
    }
    return result;
  }
  // Force a reduce, if possible. Return false if that can't
  // be done.
  /**
  @internal
  */
  forceReduce() {
    let { parser: parser2 } = this.p;
    let reduce = parser2.stateSlot(
      this.state,
      5
      /* ParseState.ForcedReduce */
    );
    if ((reduce & 65536) == 0)
      return false;
    if (!parser2.validAction(this.state, reduce)) {
      let depth = reduce >> 19, term = reduce & 65535;
      let target = this.stack.length - depth * 3;
      if (target < 0 || parser2.getGoto(this.stack[target], term, false) < 0) {
        let backup = this.findForcedReduction();
        if (backup == null)
          return false;
        reduce = backup;
      }
      this.storeNode(0, this.pos, this.pos, 4, true);
      this.score -= 100;
    }
    this.reducePos = this.pos;
    this.reduce(reduce);
    return true;
  }
  /**
  Try to scan through the automaton to find some kind of reduction
  that can be applied. Used when the regular ForcedReduce field
  isn't a valid action. @internal
  */
  findForcedReduction() {
    let { parser: parser2 } = this.p, seen = [];
    let explore = (state, depth) => {
      if (seen.includes(state))
        return;
      seen.push(state);
      return parser2.allActions(state, (action) => {
        if (action & (262144 | 131072))
          ;
        else if (action & 65536) {
          let rDepth = (action >> 19) - depth;
          if (rDepth > 1) {
            let term = action & 65535, target = this.stack.length - rDepth * 3;
            if (target >= 0 && parser2.getGoto(this.stack[target], term, false) >= 0)
              return rDepth << 19 | 65536 | term;
          }
        } else {
          let found = explore(action, depth + 1);
          if (found != null)
            return found;
        }
      });
    };
    return explore(this.state, 0);
  }
  /**
  @internal
  */
  forceAll() {
    while (!this.p.parser.stateFlag(
      this.state,
      2
      /* StateFlag.Accepting */
    )) {
      if (!this.forceReduce()) {
        this.storeNode(0, this.pos, this.pos, 4, true);
        break;
      }
    }
    return this;
  }
  /**
  Check whether this state has no further actions (assumed to be a direct descendant of the
  top state, since any other states must be able to continue
  somehow). @internal
  */
  get deadEnd() {
    if (this.stack.length != 3)
      return false;
    let { parser: parser2 } = this.p;
    return parser2.data[parser2.stateSlot(
      this.state,
      1
      /* ParseState.Actions */
    )] == 65535 && !parser2.stateSlot(
      this.state,
      4
      /* ParseState.DefaultReduce */
    );
  }
  /**
  Restart the stack (put it back in its start state). Only safe
  when this.stack.length == 3 (state is directly below the top
  state). @internal
  */
  restart() {
    this.storeNode(0, this.pos, this.pos, 4, true);
    this.state = this.stack[0];
    this.stack.length = 0;
  }
  /**
  @internal
  */
  sameState(other) {
    if (this.state != other.state || this.stack.length != other.stack.length)
      return false;
    for (let i = 0; i < this.stack.length; i += 3)
      if (this.stack[i] != other.stack[i])
        return false;
    return true;
  }
  /**
  Get the parser used by this stack.
  */
  get parser() {
    return this.p.parser;
  }
  /**
  Test whether a given dialect (by numeric ID, as exported from
  the terms file) is enabled.
  */
  dialectEnabled(dialectID) {
    return this.p.parser.dialect.flags[dialectID];
  }
  shiftContext(term, start) {
    if (this.curContext)
      this.updateContext(this.curContext.tracker.shift(this.curContext.context, term, this, this.p.stream.reset(start)));
  }
  reduceContext(term, start) {
    if (this.curContext)
      this.updateContext(this.curContext.tracker.reduce(this.curContext.context, term, this, this.p.stream.reset(start)));
  }
  /**
  @internal
  */
  emitContext() {
    let last = this.buffer.length - 1;
    if (last < 0 || this.buffer[last] != -3)
      this.buffer.push(this.curContext.hash, this.pos, this.pos, -3);
  }
  /**
  @internal
  */
  emitLookAhead() {
    let last = this.buffer.length - 1;
    if (last < 0 || this.buffer[last] != -4)
      this.buffer.push(this.lookAhead, this.pos, this.pos, -4);
  }
  updateContext(context) {
    if (context != this.curContext.context) {
      let newCx = new StackContext(this.curContext.tracker, context);
      if (newCx.hash != this.curContext.hash)
        this.emitContext();
      this.curContext = newCx;
    }
  }
  /**
  @internal
  */
  setLookAhead(lookAhead) {
    if (lookAhead > this.lookAhead) {
      this.emitLookAhead();
      this.lookAhead = lookAhead;
    }
  }
  /**
  @internal
  */
  close() {
    if (this.curContext && this.curContext.tracker.strict)
      this.emitContext();
    if (this.lookAhead > 0)
      this.emitLookAhead();
  }
};
var StackContext = class {
  constructor(tracker, context) {
    this.tracker = tracker;
    this.context = context;
    this.hash = tracker.strict ? tracker.hash(context) : 0;
  }
};
var SimulatedStack = class {
  constructor(start) {
    this.start = start;
    this.state = start.state;
    this.stack = start.stack;
    this.base = this.stack.length;
  }
  reduce(action) {
    let term = action & 65535, depth = action >> 19;
    if (depth == 0) {
      if (this.stack == this.start.stack)
        this.stack = this.stack.slice();
      this.stack.push(this.state, 0, 0);
      this.base += 3;
    } else {
      this.base -= (depth - 1) * 3;
    }
    let goto = this.start.p.parser.getGoto(this.stack[this.base - 3], term, true);
    this.state = goto;
  }
};
var StackBufferCursor = class {
  constructor(stack, pos, index) {
    this.stack = stack;
    this.pos = pos;
    this.index = index;
    this.buffer = stack.buffer;
    if (this.index == 0)
      this.maybeNext();
  }
  static create(stack, pos = stack.bufferBase + stack.buffer.length) {
    return new StackBufferCursor(stack, pos, pos - stack.bufferBase);
  }
  maybeNext() {
    let next = this.stack.parent;
    if (next != null) {
      this.index = this.stack.bufferBase - next.bufferBase;
      this.stack = next;
      this.buffer = next.buffer;
    }
  }
  get id() {
    return this.buffer[this.index - 4];
  }
  get start() {
    return this.buffer[this.index - 3];
  }
  get end() {
    return this.buffer[this.index - 2];
  }
  get size() {
    return this.buffer[this.index - 1];
  }
  next() {
    this.index -= 4;
    this.pos -= 4;
    if (this.index == 0)
      this.maybeNext();
  }
  fork() {
    return new StackBufferCursor(this.stack, this.pos, this.index);
  }
};
function decodeArray(input, Type = Uint16Array) {
  if (typeof input != "string")
    return input;
  let array = null;
  for (let pos = 0, out = 0; pos < input.length; ) {
    let value = 0;
    for (; ; ) {
      let next = input.charCodeAt(pos++), stop = false;
      if (next == 126) {
        value = 65535;
        break;
      }
      if (next >= 92)
        next--;
      if (next >= 34)
        next--;
      let digit = next - 32;
      if (digit >= 46) {
        digit -= 46;
        stop = true;
      }
      value += digit;
      if (stop)
        break;
      value *= 46;
    }
    if (array)
      array[out++] = value;
    else
      array = new Type(value);
  }
  return array;
}
var CachedToken = class {
  constructor() {
    this.start = -1;
    this.value = -1;
    this.end = -1;
    this.extended = -1;
    this.lookAhead = 0;
    this.mask = 0;
    this.context = 0;
  }
};
var nullToken = new CachedToken();
var InputStream = class {
  /**
  @internal
  */
  constructor(input, ranges) {
    this.input = input;
    this.ranges = ranges;
    this.chunk = "";
    this.chunkOff = 0;
    this.chunk2 = "";
    this.chunk2Pos = 0;
    this.next = -1;
    this.token = nullToken;
    this.rangeIndex = 0;
    this.pos = this.chunkPos = ranges[0].from;
    this.range = ranges[0];
    this.end = ranges[ranges.length - 1].to;
    this.readNext();
  }
  /**
  @internal
  */
  resolveOffset(offset, assoc) {
    let range = this.range, index = this.rangeIndex;
    let pos = this.pos + offset;
    while (pos < range.from) {
      if (!index)
        return null;
      let next = this.ranges[--index];
      pos -= range.from - next.to;
      range = next;
    }
    while (assoc < 0 ? pos > range.to : pos >= range.to) {
      if (index == this.ranges.length - 1)
        return null;
      let next = this.ranges[++index];
      pos += next.from - range.to;
      range = next;
    }
    return pos;
  }
  /**
  @internal
  */
  clipPos(pos) {
    if (pos >= this.range.from && pos < this.range.to)
      return pos;
    for (let range of this.ranges)
      if (range.to > pos)
        return Math.max(pos, range.from);
    return this.end;
  }
  /**
  Look at a code unit near the stream position. `.peek(0)` equals
  `.next`, `.peek(-1)` gives you the previous character, and so
  on.
  
  Note that looking around during tokenizing creates dependencies
  on potentially far-away content, which may reduce the
  effectiveness incremental parsing—when looking forward—or even
  cause invalid reparses when looking backward more than 25 code
  units, since the library does not track lookbehind.
  */
  peek(offset) {
    let idx = this.chunkOff + offset, pos, result;
    if (idx >= 0 && idx < this.chunk.length) {
      pos = this.pos + offset;
      result = this.chunk.charCodeAt(idx);
    } else {
      let resolved = this.resolveOffset(offset, 1);
      if (resolved == null)
        return -1;
      pos = resolved;
      if (pos >= this.chunk2Pos && pos < this.chunk2Pos + this.chunk2.length) {
        result = this.chunk2.charCodeAt(pos - this.chunk2Pos);
      } else {
        let i = this.rangeIndex, range = this.range;
        while (range.to <= pos)
          range = this.ranges[++i];
        this.chunk2 = this.input.chunk(this.chunk2Pos = pos);
        if (pos + this.chunk2.length > range.to)
          this.chunk2 = this.chunk2.slice(0, range.to - pos);
        result = this.chunk2.charCodeAt(0);
      }
    }
    if (pos >= this.token.lookAhead)
      this.token.lookAhead = pos + 1;
    return result;
  }
  /**
  Accept a token. By default, the end of the token is set to the
  current stream position, but you can pass an offset (relative to
  the stream position) to change that.
  */
  acceptToken(token, endOffset = 0) {
    let end = endOffset ? this.resolveOffset(endOffset, -1) : this.pos;
    if (end == null || end < this.token.start)
      throw new RangeError("Token end out of bounds");
    this.token.value = token;
    this.token.end = end;
  }
  /**
  Accept a token ending at a specific given position.
  */
  acceptTokenTo(token, endPos) {
    this.token.value = token;
    this.token.end = endPos;
  }
  getChunk() {
    if (this.pos >= this.chunk2Pos && this.pos < this.chunk2Pos + this.chunk2.length) {
      let { chunk, chunkPos } = this;
      this.chunk = this.chunk2;
      this.chunkPos = this.chunk2Pos;
      this.chunk2 = chunk;
      this.chunk2Pos = chunkPos;
      this.chunkOff = this.pos - this.chunkPos;
    } else {
      this.chunk2 = this.chunk;
      this.chunk2Pos = this.chunkPos;
      let nextChunk = this.input.chunk(this.pos);
      let end = this.pos + nextChunk.length;
      this.chunk = end > this.range.to ? nextChunk.slice(0, this.range.to - this.pos) : nextChunk;
      this.chunkPos = this.pos;
      this.chunkOff = 0;
    }
  }
  readNext() {
    if (this.chunkOff >= this.chunk.length) {
      this.getChunk();
      if (this.chunkOff == this.chunk.length)
        return this.next = -1;
    }
    return this.next = this.chunk.charCodeAt(this.chunkOff);
  }
  /**
  Move the stream forward N (defaults to 1) code units. Returns
  the new value of [`next`](#lr.InputStream.next).
  */
  advance(n = 1) {
    this.chunkOff += n;
    while (this.pos + n >= this.range.to) {
      if (this.rangeIndex == this.ranges.length - 1)
        return this.setDone();
      n -= this.range.to - this.pos;
      this.range = this.ranges[++this.rangeIndex];
      this.pos = this.range.from;
    }
    this.pos += n;
    if (this.pos >= this.token.lookAhead)
      this.token.lookAhead = this.pos + 1;
    return this.readNext();
  }
  setDone() {
    this.pos = this.chunkPos = this.end;
    this.range = this.ranges[this.rangeIndex = this.ranges.length - 1];
    this.chunk = "";
    return this.next = -1;
  }
  /**
  @internal
  */
  reset(pos, token) {
    if (token) {
      this.token = token;
      token.start = pos;
      token.lookAhead = pos + 1;
      token.value = token.extended = -1;
    } else {
      this.token = nullToken;
    }
    if (this.pos != pos) {
      this.pos = pos;
      if (pos == this.end) {
        this.setDone();
        return this;
      }
      while (pos < this.range.from)
        this.range = this.ranges[--this.rangeIndex];
      while (pos >= this.range.to)
        this.range = this.ranges[++this.rangeIndex];
      if (pos >= this.chunkPos && pos < this.chunkPos + this.chunk.length) {
        this.chunkOff = pos - this.chunkPos;
      } else {
        this.chunk = "";
        this.chunkOff = 0;
      }
      this.readNext();
    }
    return this;
  }
  /**
  @internal
  */
  read(from, to) {
    if (from >= this.chunkPos && to <= this.chunkPos + this.chunk.length)
      return this.chunk.slice(from - this.chunkPos, to - this.chunkPos);
    if (from >= this.chunk2Pos && to <= this.chunk2Pos + this.chunk2.length)
      return this.chunk2.slice(from - this.chunk2Pos, to - this.chunk2Pos);
    if (from >= this.range.from && to <= this.range.to)
      return this.input.read(from, to);
    let result = "";
    for (let r of this.ranges) {
      if (r.from >= to)
        break;
      if (r.to > from)
        result += this.input.read(Math.max(r.from, from), Math.min(r.to, to));
    }
    return result;
  }
};
var TokenGroup = class {
  constructor(data, id) {
    this.data = data;
    this.id = id;
  }
  token(input, stack) {
    let { parser: parser2 } = stack.p;
    readToken(this.data, input, stack, this.id, parser2.data, parser2.tokenPrecTable);
  }
};
TokenGroup.prototype.contextual = TokenGroup.prototype.fallback = TokenGroup.prototype.extend = false;
var LocalTokenGroup = class {
  constructor(data, precTable, elseToken) {
    this.precTable = precTable;
    this.elseToken = elseToken;
    this.data = typeof data == "string" ? decodeArray(data) : data;
  }
  token(input, stack) {
    let start = input.pos, skipped = 0;
    for (; ; ) {
      let atEof = input.next < 0, nextPos = input.resolveOffset(1, 1);
      readToken(this.data, input, stack, 0, this.data, this.precTable);
      if (input.token.value > -1)
        break;
      if (this.elseToken == null)
        return;
      if (!atEof)
        skipped++;
      if (nextPos == null)
        break;
      input.reset(nextPos, input.token);
    }
    if (skipped) {
      input.reset(start, input.token);
      input.acceptToken(this.elseToken, skipped);
    }
  }
};
LocalTokenGroup.prototype.contextual = TokenGroup.prototype.fallback = TokenGroup.prototype.extend = false;
var ExternalTokenizer = class {
  /**
  Create a tokenizer. The first argument is the function that,
  given an input stream, scans for the types of tokens it
  recognizes at the stream's position, and calls
  [`acceptToken`](#lr.InputStream.acceptToken) when it finds
  one.
  */
  constructor(token, options = {}) {
    this.token = token;
    this.contextual = !!options.contextual;
    this.fallback = !!options.fallback;
    this.extend = !!options.extend;
  }
};
function readToken(data, input, stack, group, precTable, precOffset) {
  let state = 0, groupMask = 1 << group, { dialect } = stack.p.parser;
  scan:
    for (; ; ) {
      if ((groupMask & data[state]) == 0)
        break;
      let accEnd = data[state + 1];
      for (let i = state + 3; i < accEnd; i += 2)
        if ((data[i + 1] & groupMask) > 0) {
          let term = data[i];
          if (dialect.allows(term) && (input.token.value == -1 || input.token.value == term || overrides(term, input.token.value, precTable, precOffset))) {
            input.acceptToken(term);
            break;
          }
        }
      let next = input.next, low = 0, high = data[state + 2];
      if (input.next < 0 && high > low && data[accEnd + high * 3 - 3] == 65535) {
        state = data[accEnd + high * 3 - 1];
        continue scan;
      }
      for (; low < high; ) {
        let mid = low + high >> 1;
        let index = accEnd + mid + (mid << 1);
        let from = data[index], to = data[index + 1] || 65536;
        if (next < from)
          high = mid;
        else if (next >= to)
          low = mid + 1;
        else {
          state = data[index + 2];
          input.advance();
          continue scan;
        }
      }
      break;
    }
}
function findOffset(data, start, term) {
  for (let i = start, next; (next = data[i]) != 65535; i++)
    if (next == term)
      return i - start;
  return -1;
}
function overrides(token, prev, tableData, tableOffset) {
  let iPrev = findOffset(tableData, tableOffset, prev);
  return iPrev < 0 || findOffset(tableData, tableOffset, token) < iPrev;
}
var verbose = typeof process != "undefined" && process.env && /\bparse\b/.test(process.env.LOG);
var stackIDs = null;
function cutAt(tree, pos, side) {
  let cursor = tree.cursor(IterMode.IncludeAnonymous);
  cursor.moveTo(pos);
  for (; ; ) {
    if (!(side < 0 ? cursor.childBefore(pos) : cursor.childAfter(pos)))
      for (; ; ) {
        if ((side < 0 ? cursor.to < pos : cursor.from > pos) && !cursor.type.isError)
          return side < 0 ? Math.max(0, Math.min(
            cursor.to - 1,
            pos - 25
            /* Lookahead.Margin */
          )) : Math.min(tree.length, Math.max(
            cursor.from + 1,
            pos + 25
            /* Lookahead.Margin */
          ));
        if (side < 0 ? cursor.prevSibling() : cursor.nextSibling())
          break;
        if (!cursor.parent())
          return side < 0 ? 0 : tree.length;
      }
  }
}
var FragmentCursor = class {
  constructor(fragments, nodeSet) {
    this.fragments = fragments;
    this.nodeSet = nodeSet;
    this.i = 0;
    this.fragment = null;
    this.safeFrom = -1;
    this.safeTo = -1;
    this.trees = [];
    this.start = [];
    this.index = [];
    this.nextFragment();
  }
  nextFragment() {
    let fr = this.fragment = this.i == this.fragments.length ? null : this.fragments[this.i++];
    if (fr) {
      this.safeFrom = fr.openStart ? cutAt(fr.tree, fr.from + fr.offset, 1) - fr.offset : fr.from;
      this.safeTo = fr.openEnd ? cutAt(fr.tree, fr.to + fr.offset, -1) - fr.offset : fr.to;
      while (this.trees.length) {
        this.trees.pop();
        this.start.pop();
        this.index.pop();
      }
      this.trees.push(fr.tree);
      this.start.push(-fr.offset);
      this.index.push(0);
      this.nextStart = this.safeFrom;
    } else {
      this.nextStart = 1e9;
    }
  }
  // `pos` must be >= any previously given `pos` for this cursor
  nodeAt(pos) {
    if (pos < this.nextStart)
      return null;
    while (this.fragment && this.safeTo <= pos)
      this.nextFragment();
    if (!this.fragment)
      return null;
    for (; ; ) {
      let last = this.trees.length - 1;
      if (last < 0) {
        this.nextFragment();
        return null;
      }
      let top = this.trees[last], index = this.index[last];
      if (index == top.children.length) {
        this.trees.pop();
        this.start.pop();
        this.index.pop();
        continue;
      }
      let next = top.children[index];
      let start = this.start[last] + top.positions[index];
      if (start > pos) {
        this.nextStart = start;
        return null;
      }
      if (next instanceof Tree) {
        if (start == pos) {
          if (start < this.safeFrom)
            return null;
          let end = start + next.length;
          if (end <= this.safeTo) {
            let lookAhead = next.prop(NodeProp.lookAhead);
            if (!lookAhead || end + lookAhead < this.fragment.to)
              return next;
          }
        }
        this.index[last]++;
        if (start + next.length >= Math.max(this.safeFrom, pos)) {
          this.trees.push(next);
          this.start.push(start);
          this.index.push(0);
        }
      } else {
        this.index[last]++;
        this.nextStart = start + next.length;
      }
    }
  }
};
var TokenCache = class {
  constructor(parser2, stream) {
    this.stream = stream;
    this.tokens = [];
    this.mainToken = null;
    this.actions = [];
    this.tokens = parser2.tokenizers.map((_) => new CachedToken());
  }
  getActions(stack) {
    let actionIndex = 0;
    let main = null;
    let { parser: parser2 } = stack.p, { tokenizers } = parser2;
    let mask = parser2.stateSlot(
      stack.state,
      3
      /* ParseState.TokenizerMask */
    );
    let context = stack.curContext ? stack.curContext.hash : 0;
    let lookAhead = 0;
    for (let i = 0; i < tokenizers.length; i++) {
      if ((1 << i & mask) == 0)
        continue;
      let tokenizer = tokenizers[i], token = this.tokens[i];
      if (main && !tokenizer.fallback)
        continue;
      if (tokenizer.contextual || token.start != stack.pos || token.mask != mask || token.context != context) {
        this.updateCachedToken(token, tokenizer, stack);
        token.mask = mask;
        token.context = context;
      }
      if (token.lookAhead > token.end + 25)
        lookAhead = Math.max(token.lookAhead, lookAhead);
      if (token.value != 0) {
        let startIndex = actionIndex;
        if (token.extended > -1)
          actionIndex = this.addActions(stack, token.extended, token.end, actionIndex);
        actionIndex = this.addActions(stack, token.value, token.end, actionIndex);
        if (!tokenizer.extend) {
          main = token;
          if (actionIndex > startIndex)
            break;
        }
      }
    }
    while (this.actions.length > actionIndex)
      this.actions.pop();
    if (lookAhead)
      stack.setLookAhead(lookAhead);
    if (!main && stack.pos == this.stream.end) {
      main = new CachedToken();
      main.value = stack.p.parser.eofTerm;
      main.start = main.end = stack.pos;
      actionIndex = this.addActions(stack, main.value, main.end, actionIndex);
    }
    this.mainToken = main;
    return this.actions;
  }
  getMainToken(stack) {
    if (this.mainToken)
      return this.mainToken;
    let main = new CachedToken(), { pos, p } = stack;
    main.start = pos;
    main.end = Math.min(pos + 1, p.stream.end);
    main.value = pos == p.stream.end ? p.parser.eofTerm : 0;
    return main;
  }
  updateCachedToken(token, tokenizer, stack) {
    let start = this.stream.clipPos(stack.pos);
    tokenizer.token(this.stream.reset(start, token), stack);
    if (token.value > -1) {
      let { parser: parser2 } = stack.p;
      for (let i = 0; i < parser2.specialized.length; i++)
        if (parser2.specialized[i] == token.value) {
          let result = parser2.specializers[i](this.stream.read(token.start, token.end), stack);
          if (result >= 0 && stack.p.parser.dialect.allows(result >> 1)) {
            if ((result & 1) == 0)
              token.value = result >> 1;
            else
              token.extended = result >> 1;
            break;
          }
        }
    } else {
      token.value = 0;
      token.end = this.stream.clipPos(start + 1);
    }
  }
  putAction(action, token, end, index) {
    for (let i = 0; i < index; i += 3)
      if (this.actions[i] == action)
        return index;
    this.actions[index++] = action;
    this.actions[index++] = token;
    this.actions[index++] = end;
    return index;
  }
  addActions(stack, token, end, index) {
    let { state } = stack, { parser: parser2 } = stack.p, { data } = parser2;
    for (let set = 0; set < 2; set++) {
      for (let i = parser2.stateSlot(
        state,
        set ? 2 : 1
        /* ParseState.Actions */
      ); ; i += 3) {
        if (data[i] == 65535) {
          if (data[i + 1] == 1) {
            i = pair(data, i + 2);
          } else {
            if (index == 0 && data[i + 1] == 2)
              index = this.putAction(pair(data, i + 2), token, end, index);
            break;
          }
        }
        if (data[i] == token)
          index = this.putAction(pair(data, i + 1), token, end, index);
      }
    }
    return index;
  }
};
var Parse = class {
  constructor(parser2, input, fragments, ranges) {
    this.parser = parser2;
    this.input = input;
    this.ranges = ranges;
    this.recovering = 0;
    this.nextStackID = 9812;
    this.minStackPos = 0;
    this.reused = [];
    this.stoppedAt = null;
    this.lastBigReductionStart = -1;
    this.lastBigReductionSize = 0;
    this.bigReductionCount = 0;
    this.stream = new InputStream(input, ranges);
    this.tokens = new TokenCache(parser2, this.stream);
    this.topTerm = parser2.top[1];
    let { from } = ranges[0];
    this.stacks = [Stack.start(this, parser2.top[0], from)];
    this.fragments = fragments.length && this.stream.end - from > parser2.bufferLength * 4 ? new FragmentCursor(fragments, parser2.nodeSet) : null;
  }
  get parsedPos() {
    return this.minStackPos;
  }
  // Move the parser forward. This will process all parse stacks at
  // `this.pos` and try to advance them to a further position. If no
  // stack for such a position is found, it'll start error-recovery.
  //
  // When the parse is finished, this will return a syntax tree. When
  // not, it returns `null`.
  advance() {
    let stacks = this.stacks, pos = this.minStackPos;
    let newStacks = this.stacks = [];
    let stopped, stoppedTokens;
    if (this.bigReductionCount > 300 && stacks.length == 1) {
      let [s] = stacks;
      while (s.forceReduce() && s.stack.length && s.stack[s.stack.length - 2] >= this.lastBigReductionStart) {
      }
      this.bigReductionCount = this.lastBigReductionSize = 0;
    }
    for (let i = 0; i < stacks.length; i++) {
      let stack = stacks[i];
      for (; ; ) {
        this.tokens.mainToken = null;
        if (stack.pos > pos) {
          newStacks.push(stack);
        } else if (this.advanceStack(stack, newStacks, stacks)) {
          continue;
        } else {
          if (!stopped) {
            stopped = [];
            stoppedTokens = [];
          }
          stopped.push(stack);
          let tok = this.tokens.getMainToken(stack);
          stoppedTokens.push(tok.value, tok.end);
        }
        break;
      }
    }
    if (!newStacks.length) {
      let finished = stopped && findFinished(stopped);
      if (finished) {
        if (verbose)
          console.log("Finish with " + this.stackID(finished));
        return this.stackToTree(finished);
      }
      if (this.parser.strict) {
        if (verbose && stopped)
          console.log("Stuck with token " + (this.tokens.mainToken ? this.parser.getName(this.tokens.mainToken.value) : "none"));
        throw new SyntaxError("No parse at " + pos);
      }
      if (!this.recovering)
        this.recovering = 5;
    }
    if (this.recovering && stopped) {
      let finished = this.stoppedAt != null && stopped[0].pos > this.stoppedAt ? stopped[0] : this.runRecovery(stopped, stoppedTokens, newStacks);
      if (finished) {
        if (verbose)
          console.log("Force-finish " + this.stackID(finished));
        return this.stackToTree(finished.forceAll());
      }
    }
    if (this.recovering) {
      let maxRemaining = this.recovering == 1 ? 1 : this.recovering * 3;
      if (newStacks.length > maxRemaining) {
        newStacks.sort((a, b) => b.score - a.score);
        while (newStacks.length > maxRemaining)
          newStacks.pop();
      }
      if (newStacks.some((s) => s.reducePos > pos))
        this.recovering--;
    } else if (newStacks.length > 1) {
      outer:
        for (let i = 0; i < newStacks.length - 1; i++) {
          let stack = newStacks[i];
          for (let j = i + 1; j < newStacks.length; j++) {
            let other = newStacks[j];
            if (stack.sameState(other) || stack.buffer.length > 500 && other.buffer.length > 500) {
              if ((stack.score - other.score || stack.buffer.length - other.buffer.length) > 0) {
                newStacks.splice(j--, 1);
              } else {
                newStacks.splice(i--, 1);
                continue outer;
              }
            }
          }
        }
      if (newStacks.length > 12)
        newStacks.splice(
          12,
          newStacks.length - 12
          /* Rec.MaxStackCount */
        );
    }
    this.minStackPos = newStacks[0].pos;
    for (let i = 1; i < newStacks.length; i++)
      if (newStacks[i].pos < this.minStackPos)
        this.minStackPos = newStacks[i].pos;
    return null;
  }
  stopAt(pos) {
    if (this.stoppedAt != null && this.stoppedAt < pos)
      throw new RangeError("Can't move stoppedAt forward");
    this.stoppedAt = pos;
  }
  // Returns an updated version of the given stack, or null if the
  // stack can't advance normally. When `split` and `stacks` are
  // given, stacks split off by ambiguous operations will be pushed to
  // `split`, or added to `stacks` if they move `pos` forward.
  advanceStack(stack, stacks, split) {
    let start = stack.pos, { parser: parser2 } = this;
    let base = verbose ? this.stackID(stack) + " -> " : "";
    if (this.stoppedAt != null && start > this.stoppedAt)
      return stack.forceReduce() ? stack : null;
    if (this.fragments) {
      let strictCx = stack.curContext && stack.curContext.tracker.strict, cxHash = strictCx ? stack.curContext.hash : 0;
      for (let cached = this.fragments.nodeAt(start); cached; ) {
        let match = this.parser.nodeSet.types[cached.type.id] == cached.type ? parser2.getGoto(stack.state, cached.type.id) : -1;
        if (match > -1 && cached.length && (!strictCx || (cached.prop(NodeProp.contextHash) || 0) == cxHash)) {
          stack.useNode(cached, match);
          if (verbose)
            console.log(base + this.stackID(stack) + ` (via reuse of ${parser2.getName(cached.type.id)})`);
          return true;
        }
        if (!(cached instanceof Tree) || cached.children.length == 0 || cached.positions[0] > 0)
          break;
        let inner = cached.children[0];
        if (inner instanceof Tree && cached.positions[0] == 0)
          cached = inner;
        else
          break;
      }
    }
    let defaultReduce = parser2.stateSlot(
      stack.state,
      4
      /* ParseState.DefaultReduce */
    );
    if (defaultReduce > 0) {
      stack.reduce(defaultReduce);
      if (verbose)
        console.log(base + this.stackID(stack) + ` (via always-reduce ${parser2.getName(
          defaultReduce & 65535
          /* Action.ValueMask */
        )})`);
      return true;
    }
    if (stack.stack.length >= 8400) {
      while (stack.stack.length > 6e3 && stack.forceReduce()) {
      }
    }
    let actions = this.tokens.getActions(stack);
    for (let i = 0; i < actions.length; ) {
      let action = actions[i++], term = actions[i++], end = actions[i++];
      let last = i == actions.length || !split;
      let localStack = last ? stack : stack.split();
      let main = this.tokens.mainToken;
      localStack.apply(action, term, main ? main.start : localStack.pos, end);
      if (verbose)
        console.log(base + this.stackID(localStack) + ` (via ${(action & 65536) == 0 ? "shift" : `reduce of ${parser2.getName(
          action & 65535
          /* Action.ValueMask */
        )}`} for ${parser2.getName(term)} @ ${start}${localStack == stack ? "" : ", split"})`);
      if (last)
        return true;
      else if (localStack.pos > start)
        stacks.push(localStack);
      else
        split.push(localStack);
    }
    return false;
  }
  // Advance a given stack forward as far as it will go. Returns the
  // (possibly updated) stack if it got stuck, or null if it moved
  // forward and was given to `pushStackDedup`.
  advanceFully(stack, newStacks) {
    let pos = stack.pos;
    for (; ; ) {
      if (!this.advanceStack(stack, null, null))
        return false;
      if (stack.pos > pos) {
        pushStackDedup(stack, newStacks);
        return true;
      }
    }
  }
  runRecovery(stacks, tokens, newStacks) {
    let finished = null, restarted = false;
    for (let i = 0; i < stacks.length; i++) {
      let stack = stacks[i], token = tokens[i << 1], tokenEnd = tokens[(i << 1) + 1];
      let base = verbose ? this.stackID(stack) + " -> " : "";
      if (stack.deadEnd) {
        if (restarted)
          continue;
        restarted = true;
        stack.restart();
        if (verbose)
          console.log(base + this.stackID(stack) + " (restarted)");
        let done = this.advanceFully(stack, newStacks);
        if (done)
          continue;
      }
      let force = stack.split(), forceBase = base;
      for (let j = 0; force.forceReduce() && j < 10; j++) {
        if (verbose)
          console.log(forceBase + this.stackID(force) + " (via force-reduce)");
        let done = this.advanceFully(force, newStacks);
        if (done)
          break;
        if (verbose)
          forceBase = this.stackID(force) + " -> ";
      }
      for (let insert of stack.recoverByInsert(token)) {
        if (verbose)
          console.log(base + this.stackID(insert) + " (via recover-insert)");
        this.advanceFully(insert, newStacks);
      }
      if (this.stream.end > stack.pos) {
        if (tokenEnd == stack.pos) {
          tokenEnd++;
          token = 0;
        }
        stack.recoverByDelete(token, tokenEnd);
        if (verbose)
          console.log(base + this.stackID(stack) + ` (via recover-delete ${this.parser.getName(token)})`);
        pushStackDedup(stack, newStacks);
      } else if (!finished || finished.score < stack.score) {
        finished = stack;
      }
    }
    return finished;
  }
  // Convert the stack's buffer to a syntax tree.
  stackToTree(stack) {
    stack.close();
    return Tree.build({
      buffer: StackBufferCursor.create(stack),
      nodeSet: this.parser.nodeSet,
      topID: this.topTerm,
      maxBufferLength: this.parser.bufferLength,
      reused: this.reused,
      start: this.ranges[0].from,
      length: stack.pos - this.ranges[0].from,
      minRepeatType: this.parser.minRepeatTerm
    });
  }
  stackID(stack) {
    let id = (stackIDs || (stackIDs = /* @__PURE__ */ new WeakMap())).get(stack);
    if (!id)
      stackIDs.set(stack, id = String.fromCodePoint(this.nextStackID++));
    return id + stack;
  }
};
function pushStackDedup(stack, newStacks) {
  for (let i = 0; i < newStacks.length; i++) {
    let other = newStacks[i];
    if (other.pos == stack.pos && other.sameState(stack)) {
      if (newStacks[i].score < stack.score)
        newStacks[i] = stack;
      return;
    }
  }
  newStacks.push(stack);
}
var Dialect = class {
  constructor(source, flags, disabled) {
    this.source = source;
    this.flags = flags;
    this.disabled = disabled;
  }
  allows(term) {
    return !this.disabled || this.disabled[term] == 0;
  }
};
var LRParser = class extends Parser {
  /**
  @internal
  */
  constructor(spec) {
    super();
    this.wrappers = [];
    if (spec.version != 14)
      throw new RangeError(`Parser version (${spec.version}) doesn't match runtime version (${14})`);
    let nodeNames = spec.nodeNames.split(" ");
    this.minRepeatTerm = nodeNames.length;
    for (let i = 0; i < spec.repeatNodeCount; i++)
      nodeNames.push("");
    let topTerms = Object.keys(spec.topRules).map((r) => spec.topRules[r][1]);
    let nodeProps = [];
    for (let i = 0; i < nodeNames.length; i++)
      nodeProps.push([]);
    function setProp(nodeID, prop, value) {
      nodeProps[nodeID].push([prop, prop.deserialize(String(value))]);
    }
    if (spec.nodeProps)
      for (let propSpec of spec.nodeProps) {
        let prop = propSpec[0];
        if (typeof prop == "string")
          prop = NodeProp[prop];
        for (let i = 1; i < propSpec.length; ) {
          let next = propSpec[i++];
          if (next >= 0) {
            setProp(next, prop, propSpec[i++]);
          } else {
            let value = propSpec[i + -next];
            for (let j = -next; j > 0; j--)
              setProp(propSpec[i++], prop, value);
            i++;
          }
        }
      }
    this.nodeSet = new NodeSet(nodeNames.map((name, i) => NodeType.define({
      name: i >= this.minRepeatTerm ? void 0 : name,
      id: i,
      props: nodeProps[i],
      top: topTerms.indexOf(i) > -1,
      error: i == 0,
      skipped: spec.skippedNodes && spec.skippedNodes.indexOf(i) > -1
    })));
    if (spec.propSources)
      this.nodeSet = this.nodeSet.extend(...spec.propSources);
    this.strict = false;
    this.bufferLength = DefaultBufferLength;
    let tokenArray = decodeArray(spec.tokenData);
    this.context = spec.context;
    this.specializerSpecs = spec.specialized || [];
    this.specialized = new Uint16Array(this.specializerSpecs.length);
    for (let i = 0; i < this.specializerSpecs.length; i++)
      this.specialized[i] = this.specializerSpecs[i].term;
    this.specializers = this.specializerSpecs.map(getSpecializer);
    this.states = decodeArray(spec.states, Uint32Array);
    this.data = decodeArray(spec.stateData);
    this.goto = decodeArray(spec.goto);
    this.maxTerm = spec.maxTerm;
    this.tokenizers = spec.tokenizers.map((value) => typeof value == "number" ? new TokenGroup(tokenArray, value) : value);
    this.topRules = spec.topRules;
    this.dialects = spec.dialects || {};
    this.dynamicPrecedences = spec.dynamicPrecedences || null;
    this.tokenPrecTable = spec.tokenPrec;
    this.termNames = spec.termNames || null;
    this.maxNode = this.nodeSet.types.length - 1;
    this.dialect = this.parseDialect();
    this.top = this.topRules[Object.keys(this.topRules)[0]];
  }
  createParse(input, fragments, ranges) {
    let parse = new Parse(this, input, fragments, ranges);
    for (let w of this.wrappers)
      parse = w(parse, input, fragments, ranges);
    return parse;
  }
  /**
  Get a goto table entry @internal
  */
  getGoto(state, term, loose = false) {
    let table = this.goto;
    if (term >= table[0])
      return -1;
    for (let pos = table[term + 1]; ; ) {
      let groupTag = table[pos++], last = groupTag & 1;
      let target = table[pos++];
      if (last && loose)
        return target;
      for (let end = pos + (groupTag >> 1); pos < end; pos++)
        if (table[pos] == state)
          return target;
      if (last)
        return -1;
    }
  }
  /**
  Check if this state has an action for a given terminal @internal
  */
  hasAction(state, terminal) {
    let data = this.data;
    for (let set = 0; set < 2; set++) {
      for (let i = this.stateSlot(
        state,
        set ? 2 : 1
        /* ParseState.Actions */
      ), next; ; i += 3) {
        if ((next = data[i]) == 65535) {
          if (data[i + 1] == 1)
            next = data[i = pair(data, i + 2)];
          else if (data[i + 1] == 2)
            return pair(data, i + 2);
          else
            break;
        }
        if (next == terminal || next == 0)
          return pair(data, i + 1);
      }
    }
    return 0;
  }
  /**
  @internal
  */
  stateSlot(state, slot) {
    return this.states[state * 6 + slot];
  }
  /**
  @internal
  */
  stateFlag(state, flag) {
    return (this.stateSlot(
      state,
      0
      /* ParseState.Flags */
    ) & flag) > 0;
  }
  /**
  @internal
  */
  validAction(state, action) {
    return !!this.allActions(state, (a) => a == action ? true : null);
  }
  /**
  @internal
  */
  allActions(state, action) {
    let deflt = this.stateSlot(
      state,
      4
      /* ParseState.DefaultReduce */
    );
    let result = deflt ? action(deflt) : void 0;
    for (let i = this.stateSlot(
      state,
      1
      /* ParseState.Actions */
    ); result == null; i += 3) {
      if (this.data[i] == 65535) {
        if (this.data[i + 1] == 1)
          i = pair(this.data, i + 2);
        else
          break;
      }
      result = action(pair(this.data, i + 1));
    }
    return result;
  }
  /**
  Get the states that can follow this one through shift actions or
  goto jumps. @internal
  */
  nextStates(state) {
    let result = [];
    for (let i = this.stateSlot(
      state,
      1
      /* ParseState.Actions */
    ); ; i += 3) {
      if (this.data[i] == 65535) {
        if (this.data[i + 1] == 1)
          i = pair(this.data, i + 2);
        else
          break;
      }
      if ((this.data[i + 2] & 65536 >> 16) == 0) {
        let value = this.data[i + 1];
        if (!result.some((v, i2) => i2 & 1 && v == value))
          result.push(this.data[i], value);
      }
    }
    return result;
  }
  /**
  Configure the parser. Returns a new parser instance that has the
  given settings modified. Settings not provided in `config` are
  kept from the original parser.
  */
  configure(config) {
    let copy = Object.assign(Object.create(LRParser.prototype), this);
    if (config.props)
      copy.nodeSet = this.nodeSet.extend(...config.props);
    if (config.top) {
      let info = this.topRules[config.top];
      if (!info)
        throw new RangeError(`Invalid top rule name ${config.top}`);
      copy.top = info;
    }
    if (config.tokenizers)
      copy.tokenizers = this.tokenizers.map((t) => {
        let found = config.tokenizers.find((r) => r.from == t);
        return found ? found.to : t;
      });
    if (config.specializers) {
      copy.specializers = this.specializers.slice();
      copy.specializerSpecs = this.specializerSpecs.map((s, i) => {
        let found = config.specializers.find((r) => r.from == s.external);
        if (!found)
          return s;
        let spec = Object.assign(Object.assign({}, s), { external: found.to });
        copy.specializers[i] = getSpecializer(spec);
        return spec;
      });
    }
    if (config.contextTracker)
      copy.context = config.contextTracker;
    if (config.dialect)
      copy.dialect = this.parseDialect(config.dialect);
    if (config.strict != null)
      copy.strict = config.strict;
    if (config.wrap)
      copy.wrappers = copy.wrappers.concat(config.wrap);
    if (config.bufferLength != null)
      copy.bufferLength = config.bufferLength;
    return copy;
  }
  /**
  Tells you whether any [parse wrappers](#lr.ParserConfig.wrap)
  are registered for this parser.
  */
  hasWrappers() {
    return this.wrappers.length > 0;
  }
  /**
  Returns the name associated with a given term. This will only
  work for all terms when the parser was generated with the
  `--names` option. By default, only the names of tagged terms are
  stored.
  */
  getName(term) {
    return this.termNames ? this.termNames[term] : String(term <= this.maxNode && this.nodeSet.types[term].name || term);
  }
  /**
  The eof term id is always allocated directly after the node
  types. @internal
  */
  get eofTerm() {
    return this.maxNode + 1;
  }
  /**
  The type of top node produced by the parser.
  */
  get topNode() {
    return this.nodeSet.types[this.top[1]];
  }
  /**
  @internal
  */
  dynamicPrecedence(term) {
    let prec = this.dynamicPrecedences;
    return prec == null ? 0 : prec[term] || 0;
  }
  /**
  @internal
  */
  parseDialect(dialect) {
    let values = Object.keys(this.dialects), flags = values.map(() => false);
    if (dialect)
      for (let part of dialect.split(" ")) {
        let id = values.indexOf(part);
        if (id >= 0)
          flags[id] = true;
      }
    let disabled = null;
    for (let i = 0; i < values.length; i++)
      if (!flags[i]) {
        for (let j = this.dialects[values[i]], id; (id = this.data[j++]) != 65535; )
          (disabled || (disabled = new Uint8Array(this.maxTerm + 1)))[id] = 1;
      }
    return new Dialect(dialect, flags, disabled);
  }
  /**
  Used by the output of the parser generator. Not available to
  user code. @hide
  */
  static deserialize(spec) {
    return new LRParser(spec);
  }
};
function pair(data, off) {
  return data[off] | data[off + 1] << 16;
}
function findFinished(stacks) {
  let best = null;
  for (let stack of stacks) {
    let stopped = stack.p.stoppedAt;
    if ((stack.pos == stack.p.stream.end || stopped != null && stack.pos > stopped) && stack.p.parser.stateFlag(
      stack.state,
      2
      /* StateFlag.Accepting */
    ) && (!best || best.score < stack.score))
      best = stack;
  }
  return best;
}
function getSpecializer(spec) {
  if (spec.external) {
    let mask = spec.extend ? 1 : 0;
    return (value, stack) => spec.external(value, stack) << 1 | mask;
  }
  return spec.get;
}

// externalTokens.js
var TakeInput = new ExternalTokenizer((input, stack) => {
  let pos = input.pos;
  if (input.read(pos, pos + 4) === "Take") {
    pos += 4;
  } else {
    return;
  }
  const start = pos;
  while (pos < input.end && input.read(pos, pos + 1) !== ":" && input.read(pos, pos + 1) != "\n") {
    pos++;
  }
  console.log("Captured token:");
  console.log(input.read(start, pos));
  console.log(pos);
  console.log(input.end);
  console.log();
  if (pos < input.end) {
    input.acceptToken(TakeInput, pos);
  }
}, { contextual: true });

// syntax.js
var parser = LRParser.deserialize({
  version: 14,
  states: "(pQYQQOOO!yOPO'#CaOOQO'#Ca'#CaO#OOpO'#CaO#TOpO'#CaO#YOpO'#CaO#_OpO'#CaO#dOpO'#CaO#iOpO'#CaO#nOpO'#CaO#sOpO'#CaO#xOpO'#CaO#}OpO'#CaO$SQSO'#C`OOQO'#Ce'#CeQYQQOOO$XOQO,58{O$^OpO,58{O$cOWO,58{O$hOWO,58{O$mOQO,58{O$xOWO,58{O$}OWO,58{O%SO`O,58{O%XOWO,58{O%dOQO,58{O%iOQO,58{OOQO,58z,58zOOQO-E6c-E6cO%nOpO1G.gOOQO1G.g1G.gO%sOpO1G.gO%xOpO1G.gO%}OpO1G.gO&SOpO1G.gO&XOpO7+$RO&^OQO7+$RO&fOQO7+$RO&kOQO7+$RO&pOQO7+$ROOQO<<Gm<<GmO&uOpO<<GmO&zOQO<<GmO'POpO<<GmO'UOQOAN=XO'ZOpOAN=XO'`OQOAN=XOOQOG22sG22sO'eOQOG22sO'jOpOG22sO'oOpOLD(_O'tOQOLD(_O'yOQO!$'KyO(OOpO!$'KyO(TOpO!)9AeO(YOQO!)9AeO(_OQO!.K7POOQO!.K7P!.K7POOQO!4/,k!4/,k",
  stateData: "(d~O[OSQOS~O]PO_QO`QOaQObQOcQOdROeROfROgSOiROjROkROlROmROnROoROpTOrUOtVOvWOzXO|YO!SZO!V[O~OP`O~OUaO~OUbO~OUcO~OUdO~OUeO~OUfO~OUgO~OUhO~OUiO~OUjO~OWkO~O^mO~OVnO~OhnO~OqmO~OsmOxmOymO~OumO~OwmO~O{mO~O}oO!QpO!RqO~O!TrO~O!WpO~OUsO~OUtO~OUuO~OUvO~OUwO~OVxO~O!OxO!PyO~O!OxO~O!OzO~O!P{O~OU|O~O!S}O~OU!OO~O!O!PO~OU!QO~O!U!RO~O!T!SO~OU!TO~OU!UO~O!P!VO~O!U!WO~OU!XO~OU!YO~O!O!ZO~O!O![O~O",
  goto: "iYPPPPZ_PPPcT^O_T]O_Q_ORl_",
  nodeNames: "\u26A0 TakeInput Comment Program Sentence WaterproofTactic TacticInput dotSpace CoqSentence",
  maxTerm: 54,
  skippedNodes: [0, 2],
  repeatNodeCount: 1,
  tokenData: "%/c~RqOX#YXY#wYZ#wZ]#Y]^#w^p#Ypq$]qx#Yxy/fyz2jz!O#Y!P![#Y![!]!+j!]!c#Y!c!d!,O!d!e!2W!e!f!8b!f!g!Ba!g!h!E{!h!j#Y!j!k#(k!k!l#*p!l!q#Y!q!r#@l!r!u#Y!u!v#Gx!v!w#Kd!w!x#Md!x!y#Y!y!z$ d!z;'S#Y;'S;=`#q<%lO#YS#]TO!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#YS#qOWSS#tP;=`<%l#YU#|T[UO!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#Yn$b][UOy#Yyz%Zz!O#Y!O!P#l!P![#Y![!]%t!]#T#Y#T#U'^#U#]#Y#]#^.O#^;'S#Y;'S;=`#q<%lO#Y[%^TO!O#Y!O!P%m!P;'S#Y;'S;=`#q<%lO#Y[%tOhWWSl%wVO!O#Y!O!P#l!P!_#Y!_!`&^!`;'S#Y;'S;=`#q<%lO#Yl&cVwWOp#Ypq&xq!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#Yd&}T{`O!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#Y['aVO!O#Y!O!P#l!P#V#Y#V#W'v#W;'S#Y;'S;=`#q<%lO#Y['yVO!O#Y!O!P#l!P#V#Y#V#W(`#W;'S#Y;'S;=`#q<%lO#Y[(cVO!O#Y!O!P#l!P#c#Y#c#d(x#d;'S#Y;'S;=`#q<%lO#Y[({VO!O#Y!O!P#l!P#f#Y#f#g)b#g;'S#Y;'S;=`#q<%lO#Y[)eVO!O#Y!O!P#l!P#W#Y#W#X)z#X;'S#Y;'S;=`#q<%lO#Y[)}VO!O#Y!O!P#l!P#]#Y#]#^*d#^;'S#Y;'S;=`#q<%lO#Y[*gVO!O#Y!O!P#l!P#b#Y#b#c*|#c;'S#Y;'S;=`#q<%lO#Y[+PVO!O#Y!O!P#l!P#Z#Y#Z#[+f#[;'S#Y;'S;=`#q<%lO#Y[+iVOp#Ypq,Oq!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#Y[,RVO!O#Y!O!P#l!P#h#Y#h#i,h#i;'S#Y;'S;=`#q<%lO#Y[,kVO!O#Y!O!P#l!P#c#Y#c#d-Q#d;'S#Y;'S;=`#q<%lO#Y[-TVOp#Ypq-jq!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#Y[-oTuWO!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#Y[.RVO!O#Y!O!P#l!P#b#Y#b#c.h#c;'S#Y;'S;=`#q<%lO#Y[.kVOp#Ypq/Qq!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#Y[/VTqWO!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#Y~/iXOv#Yvw0Uwz#Yz{1S{!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#YU0XVOp#Ypq0nq!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#YU0sTgQO!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#Y~1VVOz#Yz{1l{!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#Y~1oVOy#Yyz2Uz!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#Y~2ZTQ~O!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#Y^2mVOp#Ypq3Sq!O#Y!O!P!+c!P;'S#Y;'S;=`#q<%lO#Y^3V`Ox#Yxy4Xy!O#Y!O!P#l!P#T#Y#T#U4m#U#V7V#V#]#Y#]#^:X#^#c#Y#c#dNR#d#k#Y#k#l!!R#l;'S#Y;'S;=`#q<%lO#YU4^T!PQO!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#YU4pVO!O#Y!O!P#l!P#b#Y#b#c5V#c;'S#Y;'S;=`#q<%lO#YU5YVO!O#Y!O!P#l!P#W#Y#W#X5o#X;'S#Y;'S;=`#q<%lO#YU5rVOp#Ypq6Xq!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#YU6[VOx#Yxy6qy!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#YU6vT!UQO!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#YU7YVO!O#Y!O!P#l!P#c#Y#c#d7o#d;'S#Y;'S;=`#q<%lO#YU7rVO!O#Y!O!P#l!P#h#Y#h#i8X#i;'S#Y;'S;=`#q<%lO#YU8[VO!O#Y!O!P#l!P#[#Y#[#]8q#];'S#Y;'S;=`#q<%lO#YU8tVOp#Ypq9Zq!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#YU9^VOx#Yxy9sy!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#YU9xT!TQO!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#Y^:[VO!O#Y!O!P#l!P#h#Y#h#i:q#i;'S#Y;'S;=`#q<%lO#Y^:tVOp#Ypq;Zq!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#Y^;^XO!O#Y!O!P#l!P#[#Y#[#];y#]#g#Y#g#hBT#h;'S#Y;'S;=`#q<%lO#Y^;|VO!O#Y!O!P#l!P#c#Y#c#d<c#d;'S#Y;'S;=`#q<%lO#Y^<fVO!O#Y!O!P#l!P#`#Y#`#a<{#a;'S#Y;'S;=`#q<%lO#Y^=OVO!O#Y!O!P#l!P#W#Y#W#X=e#X;'S#Y;'S;=`#q<%lO#Y^=hVO!O#Y!O!P#l!P#g#Y#g#h=}#h;'S#Y;'S;=`#q<%lO#Y^>QVOp#Ypq>gq!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#Y^>jVO!O#Y!O!P#l!P#h#Y#h#i?P#i;'S#Y;'S;=`#q<%lO#Y^?SVO!O#Y!O!P#l!P#[#Y#[#]?i#];'S#Y;'S;=`#q<%lO#Y^?lVO!O#Y!O!P#l!P#T#Y#T#U@R#U;'S#Y;'S;=`#q<%lO#Y^@UVO!O#Y!O!P#l!P#h#Y#h#i@k#i;'S#Y;'S;=`#q<%lO#Y^@nVOp#YpqATq!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#Y^AYVyQOx#YxyAoy!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#Y[AtT}WO!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#Y^BWVO!O#Y!O!P#l!P#i#Y#i#jBm#j;'S#Y;'S;=`#q<%lO#Y^BpVO!O#Y!O!P#l!P#Y#Y#Y#ZCV#Z;'S#Y;'S;=`#q<%lO#Y^CYVO!O#Y!O!P#l!P#Y#Y#Y#ZCo#Z;'S#Y;'S;=`#q<%lO#Y^CrVO!O#Y!O!P#l!P#]#Y#]#^DX#^;'S#Y;'S;=`#q<%lO#Y^D[VO!O#Y!O!P#l!P#V#Y#V#WDq#W;'S#Y;'S;=`#q<%lO#Y^DtVO!O#Y!O!P#l!P#X#Y#X#YEZ#Y;'S#Y;'S;=`#q<%lO#Y^E^VO!O#Y!O!P#l!P#g#Y#g#hEs#h;'S#Y;'S;=`#q<%lO#Y^EvVOp#YpqF]q!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#Y^F`VO!O#Y!O!P#l!P#h#Y#h#iFu#i;'S#Y;'S;=`#q<%lO#Y^FxVO!O#Y!O!P#l!P#c#Y#c#dG_#d;'S#Y;'S;=`#q<%lO#Y^GbVOp#YpqGwq!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#Y^GzVO!O#Y!O!P#l!P#g#Y#g#hHa#h;'S#Y;'S;=`#q<%lO#Y^HdVO!O#Y!O!P#l!P#[#Y#[#]Hy#];'S#Y;'S;=`#q<%lO#Y^H|VO!O#Y!O!P#l!P#c#Y#c#dIc#d;'S#Y;'S;=`#q<%lO#Y^IfVO!O#Y!O!P#l!P#k#Y#k#lI{#l;'S#Y;'S;=`#q<%lO#Y^JOVOp#YpqJeq!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#Y^JhVO!O#Y!O!P#l!P#h#Y#h#iJ}#i;'S#Y;'S;=`#q<%lO#Y^KQVO!O#Y!O!P#l!P#[#Y#[#]Kg#];'S#Y;'S;=`#q<%lO#Y^KjVO!O#Y!O!P#l!P#T#Y#T#ULP#U;'S#Y;'S;=`#q<%lO#Y^LSVO!O#Y!O!P#l!P#h#Y#h#iLi#i;'S#Y;'S;=`#q<%lO#Y^LlVOp#YpqMRq!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#Y^MWVsQOx#YxyMmy!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#Y[MrT!RWO!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#YUNUVO!O#Y!O!P#l!P#f#Y#f#gNk#g;'S#Y;'S;=`#q<%lO#YUNnVOp#Ypq! Tq!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#YU! WVOx#Yxy! my!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#YU! rT!WQO!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#Y^!!UVO!O#Y!O!P#l!P#X#Y#X#Y!!k#Y;'S#Y;'S;=`#q<%lO#Y^!!nVOp#Ypq!#Tq!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#Y^!#WVO!O#Y!O!P#l!P#V#Y#V#W!#m#W;'S#Y;'S;=`#q<%lO#Y^!#pVO!O#Y!O!P#l!P#c#Y#c#d!$V#d;'S#Y;'S;=`#q<%lO#Y^!$YVO!O#Y!O!P#l!P#b#Y#b#c!$o#c;'S#Y;'S;=`#q<%lO#Y^!$rVO!O#Y!O!P#l!P#V#Y#V#W!%X#W;'S#Y;'S;=`#q<%lO#Y^!%[VO!O#Y!O!P#l!P#`#Y#`#a!%q#a;'S#Y;'S;=`#q<%lO#Y^!%tVO!O#Y!O!P#l!P#i#Y#i#j!&Z#j;'S#Y;'S;=`#q<%lO#Y^!&^VO!O#Y!O!P#l!P#W#Y#W#X!&s#X;'S#Y;'S;=`#q<%lO#Y^!&vVO!O#Y!O!P#l!P#X#Y#X#Y!']#Y;'S#Y;'S;=`#q<%lO#Y^!'`VOp#Ypq!'uq!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#Y^!'xVO!O#Y!O!P#l!P#h#Y#h#i!(_#i;'S#Y;'S;=`#q<%lO#Y^!(bVO!O#Y!O!P#l!P#[#Y#[#]!(w#];'S#Y;'S;=`#q<%lO#Y^!(zVO!O#Y!O!P#l!P#T#Y#T#U!)a#U;'S#Y;'S;=`#q<%lO#Y^!)dVO!O#Y!O!P#l!P#h#Y#h#i!)y#i;'S#Y;'S;=`#q<%lO#Y^!)|VOp#Ypq!*cq!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#Y^!*hVxQOx#Yxy!*}y!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#Y[!+ST!QWO!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#YU!+jO!OQWSU!+oT^QO!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#YU!,RVO!O#Y!O!P#l!P#g#Y#g#h!,h#h;'S#Y;'S;=`#q<%lO#YU!,kVO!O#Y!O!P#l!P#g#Y#g#h!-Q#h;'S#Y;'S;=`#q<%lO#YU!-TVO!O#Y!O!P#l!P#i#Y#i#j!-j#j;'S#Y;'S;=`#q<%lO#YU!-mVO!O#Y!O!P#l!P#a#Y#a#b!.S#b;'S#Y;'S;=`#q<%lO#YU!.VVO!O#Y!O!P#l!P#X#Y#X#Y!.l#Y;'S#Y;'S;=`#q<%lO#YU!.oVOp#Ypq!/Uq!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#YU!/XVO!O#Y!O!P#l!P#h#Y#h#i!/n#i;'S#Y;'S;=`#q<%lO#YU!/qVO!O#Y!O!P#l!P#[#Y#[#]!0W#];'S#Y;'S;=`#q<%lO#YU!0ZVO!O#Y!O!P#l!P#T#Y#T#U!0p#U;'S#Y;'S;=`#q<%lO#YU!0sVO!O#Y!O!P#l!P#h#Y#h#i!1Y#i;'S#Y;'S;=`#q<%lO#YU!1]VOp#Ypq!1rq!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#YU!1wTfQO!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#YU!2ZXO!O#Y!O!P#l!P#X#Y#X#Y!2v#Y#m#Y#m#n!6z#n;'S#Y;'S;=`#q<%lO#YU!2yVO!O#Y!O!P#l!P#V#Y#V#W!3`#W;'S#Y;'S;=`#q<%lO#YU!3cVO!O#Y!O!P#l!P#T#Y#T#U!3x#U;'S#Y;'S;=`#q<%lO#YU!3{VO!O#Y!O!P#l!P#i#Y#i#j!4b#j;'S#Y;'S;=`#q<%lO#YU!4eVO!O#Y!O!P#l!P#g#Y#g#h!4z#h;'S#Y;'S;=`#q<%lO#YU!4}VO!O#Y!O!P#l!P#X#Y#X#Y!5d#Y;'S#Y;'S;=`#q<%lO#YU!5gVOp#Ypq!5|q!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#YU!6PVOx#Yxy!6fy!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#YU!6kT!SQO!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#YU!6}VOp#Ypq!7dq!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#YU!7gVOx#Yxy!7|y!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#YU!8RTrQO!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#YU!8eXO!O#Y!O!P#l!P#[#Y#[#]!9Q#]#c#Y#c#d!<S#d;'S#Y;'S;=`#q<%lO#YU!9TVO!O#Y!O!P#l!P#c#Y#c#d!9j#d;'S#Y;'S;=`#q<%lO#YU!9mVO!O#Y!O!P#l!P#c#Y#c#d!:S#d;'S#Y;'S;=`#q<%lO#YU!:VVO!O#Y!O!P#l!P#g#Y#g#h!:l#h;'S#Y;'S;=`#q<%lO#YU!:oVO!O#Y!O!P#l!P#X#Y#X#Y!;U#Y;'S#Y;'S;=`#q<%lO#YU!;XVOp#Ypq!;nq!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#YU!;sTvQO!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#YU!<VVO!O#Y!O!P#l!P#b#Y#b#c!<l#c;'S#Y;'S;=`#q<%lO#YU!<oVO!O#Y!O!P#l!P#h#Y#h#i!=U#i;'S#Y;'S;=`#q<%lO#YU!=XVO!O#Y!O!P#l!P#f#Y#f#g!=n#g;'S#Y;'S;=`#q<%lO#YU!=qVO!O#Y!O!P#l!P#T#Y#T#U!>W#U;'S#Y;'S;=`#q<%lO#YU!>ZVO!O#Y!O!P#l!P#W#Y#W#X!>p#X;'S#Y;'S;=`#q<%lO#YU!>sVO!O#Y!O!P#l!P#]#Y#]#^!?Y#^;'S#Y;'S;=`#q<%lO#YU!?]VO!O#Y!O!P#l!P#V#Y#V#W!?r#W;'S#Y;'S;=`#q<%lO#YU!?uVO!O#Y!O!P#l!P#h#Y#h#i!@[#i;'S#Y;'S;=`#q<%lO#YU!@_VO!O#Y!O!P#l!P#]#Y#]#^!@t#^;'S#Y;'S;=`#q<%lO#YU!@wVO!O#Y!O!P#l!P#c#Y#c#d!A^#d;'S#Y;'S;=`#q<%lO#YU!AaVO!O#Y!O!P#l!P#b#Y#b#c!Av#c;'S#Y;'S;=`#q<%lO#YU!AyTO!O#Y!O!P!BY!P;'S#Y;'S;=`#q<%lO#YU!BaOaQWSU!BdVO!O#Y!O!P#l!P#X#Y#X#Y!By#Y;'S#Y;'S;=`#q<%lO#YU!B|VO!O#Y!O!P#l!P#Y#Y#Y#Z!Cc#Z;'S#Y;'S;=`#q<%lO#YU!CfVO!O#Y!O!P#l!P#]#Y#]#^!C{#^;'S#Y;'S;=`#q<%lO#YU!DOVO!O#Y!O!P#l!P#b#Y#b#c!De#c;'S#Y;'S;=`#q<%lO#YU!DhVO!O#Y!O!P#l!P#X#Y#X#Y!D}#Y;'S#Y;'S;=`#q<%lO#YU!EQVOp#Ypq!Egq!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#YU!ElTzQO!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#YU!FOXO!O#Y!O!P#l!P#]#Y#]#^!Fk#^#l#Y#l#m!JV#m;'S#Y;'S;=`#q<%lO#YU!FnVO!O#Y!O!P#l!P#h#Y#h#i!GT#i;'S#Y;'S;=`#q<%lO#YU!GWVO!O#Y!O!P#l!P#[#Y#[#]!Gm#];'S#Y;'S;=`#q<%lO#YU!GpVO!O#Y!O!P#l!P#X#Y#X#Y!HV#Y;'S#Y;'S;=`#q<%lO#YU!HYVO!O#Y!O!P#l!P#f#Y#f#g!Ho#g;'S#Y;'S;=`#q<%lO#YU!HrVOp#Ypq!IXq!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#YU!I[VOx#Yxy!Iqy!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#YU!IvT!VQO!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#YU!JYVO!O#Y!O!P#l!P#d#Y#d#e!Jo#e;'S#Y;'S;=`#q<%lO#YU!JrVO!O#Y!O!P#l!P#T#Y#T#U!KX#U;'S#Y;'S;=`#q<%lO#YU!K[VO!O#Y!O!P#l!P#b#Y#b#c!Kq#c;'S#Y;'S;=`#q<%lO#YU!KtVO!O#Y!O!P#l!P#W#Y#W#X!LZ#X;'S#Y;'S;=`#q<%lO#YU!L^VOp#Ypq!Lsq!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#YU!LvVO!O#Y!O!P#l!P#h#Y#h#i!M]#i;'S#Y;'S;=`#q<%lO#YU!M`VO!O#Y!O!P#l!P#[#Y#[#]!Mu#];'S#Y;'S;=`#q<%lO#YU!MxVO!O#Y!O!P#l!P#X#Y#X#Y!N_#Y;'S#Y;'S;=`#q<%lO#YU!NbVOp#Ypq!Nwq!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#YU!NzVO!O#Y!O!P#l!P#W#Y#W#X# a#X;'S#Y;'S;=`#q<%lO#YU# dVO!O#Y!O!P#l!P#X#Y#X#Y# y#Y;'S#Y;'S;=`#q<%lO#YU# |VO!O#Y!O!P#l!P#Y#Y#Y#Z#!c#Z;'S#Y;'S;=`#q<%lO#YU#!fVO!O#Y!O!P#l!P#]#Y#]#^#!{#^;'S#Y;'S;=`#q<%lO#YU##OVO!O#Y!O!P#l!P#b#Y#b#c##e#c;'S#Y;'S;=`#q<%lO#YU##hVO!O#Y!O!P#l!P#]#Y#]#^##}#^;'S#Y;'S;=`#q<%lO#YU#$QVO!O#Y!O!P#l!P#h#Y#h#i#$g#i;'S#Y;'S;=`#q<%lO#YU#$jVO!O#Y!O!P#l!P#]#Y#]#^#%P#^;'S#Y;'S;=`#q<%lO#YU#%SVO!O#Y!O!P#l!P#c#Y#c#d#%i#d;'S#Y;'S;=`#q<%lO#YU#%lVO!O#Y!O!P#l!P#b#Y#b#c#&R#c;'S#Y;'S;=`#q<%lO#YU#&UVOp#Ypq#&kq!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#YU#&nVO!O#Y!O!P#l!P#c#Y#c#d#'T#d;'S#Y;'S;=`#q<%lO#YU#'WVO!O#Y!O!P#l!P#Y#Y#Y#Z#'m#Z;'S#Y;'S;=`#q<%lO#YU#'pVOp#Ypq#(Vq!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#YU#([TpQO!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#YU#(nVO!O#Y!O!P#l!P#X#Y#X#Y#)T#Y;'S#Y;'S;=`#q<%lO#YU#)WVO!O#Y!O!P#l!P#`#Y#`#a#)m#a;'S#Y;'S;=`#q<%lO#YU#)pVO!O#Y!O!P#l!P#d#Y#d#e#*V#e;'S#Y;'S;=`#q<%lO#YU#*YTO!O#Y!O!P#*i!P;'S#Y;'S;=`#q<%lO#YU#*pO_QWSU#*sXO!O#Y!O!P#l!P#b#Y#b#c#+`#c#h#Y#h#i#.b#i;'S#Y;'S;=`#q<%lO#YU#+cVO!O#Y!O!P#l!P#W#Y#W#X#+x#X;'S#Y;'S;=`#q<%lO#YU#+{VO!O#Y!O!P#l!P#X#Y#X#Y#,b#Y;'S#Y;'S;=`#q<%lO#YU#,eVO!O#Y!O!P#l!P#X#Y#X#Y#,z#Y;'S#Y;'S;=`#q<%lO#YU#,}VO!O#Y!O!P#l!P#W#Y#W#X#-d#X;'S#Y;'S;=`#q<%lO#YU#-gVOp#Ypq#-|q!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#YU#.RToQO!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#YU#.eVOp#Ypq#.zq!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#YU#.}XO!O#Y!O!P#l!P#[#Y#[#]#/j#]#g#Y#g#h#5Y#h;'S#Y;'S;=`#q<%lO#YU#/mVO!O#Y!O!P#l!P#c#Y#c#d#0S#d;'S#Y;'S;=`#q<%lO#YU#0VVO!O#Y!O!P#l!P#`#Y#`#a#0l#a;'S#Y;'S;=`#q<%lO#YU#0oVO!O#Y!O!P#l!P#W#Y#W#X#1U#X;'S#Y;'S;=`#q<%lO#YU#1XVO!O#Y!O!P#l!P#g#Y#g#h#1n#h;'S#Y;'S;=`#q<%lO#YU#1qVOp#Ypq#2Wq!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#YU#2ZVO!O#Y!O!P#l!P#h#Y#h#i#2p#i;'S#Y;'S;=`#q<%lO#YU#2sVO!O#Y!O!P#l!P#[#Y#[#]#3Y#];'S#Y;'S;=`#q<%lO#YU#3]VO!O#Y!O!P#l!P#T#Y#T#U#3r#U;'S#Y;'S;=`#q<%lO#YU#3uVO!O#Y!O!P#l!P#h#Y#h#i#4[#i;'S#Y;'S;=`#q<%lO#YU#4_VOp#Ypq#4tq!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#YU#4yTkQO!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#YU#5]VO!O#Y!O!P#l!P#i#Y#i#j#5r#j;'S#Y;'S;=`#q<%lO#YU#5uVO!O#Y!O!P#l!P#Y#Y#Y#Z#6[#Z;'S#Y;'S;=`#q<%lO#YU#6_VO!O#Y!O!P#l!P#Y#Y#Y#Z#6t#Z;'S#Y;'S;=`#q<%lO#YU#6wVO!O#Y!O!P#l!P#]#Y#]#^#7^#^;'S#Y;'S;=`#q<%lO#YU#7aVO!O#Y!O!P#l!P#V#Y#V#W#7v#W;'S#Y;'S;=`#q<%lO#YU#7yVO!O#Y!O!P#l!P#X#Y#X#Y#8`#Y;'S#Y;'S;=`#q<%lO#YU#8cVO!O#Y!O!P#l!P#g#Y#g#h#8x#h;'S#Y;'S;=`#q<%lO#YU#8{VOp#Ypq#9bq!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#YU#9eVO!O#Y!O!P#l!P#h#Y#h#i#9z#i;'S#Y;'S;=`#q<%lO#YU#9}VO!O#Y!O!P#l!P#c#Y#c#d#:d#d;'S#Y;'S;=`#q<%lO#YU#:gVOp#Ypq#:|q!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#YU#;PVO!O#Y!O!P#l!P#g#Y#g#h#;f#h;'S#Y;'S;=`#q<%lO#YU#;iVO!O#Y!O!P#l!P#[#Y#[#]#<O#];'S#Y;'S;=`#q<%lO#YU#<RVO!O#Y!O!P#l!P#c#Y#c#d#<h#d;'S#Y;'S;=`#q<%lO#YU#<kVO!O#Y!O!P#l!P#k#Y#k#l#=Q#l;'S#Y;'S;=`#q<%lO#YU#=TVOp#Ypq#=jq!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#YU#=mVO!O#Y!O!P#l!P#h#Y#h#i#>S#i;'S#Y;'S;=`#q<%lO#YU#>VVO!O#Y!O!P#l!P#[#Y#[#]#>l#];'S#Y;'S;=`#q<%lO#YU#>oVO!O#Y!O!P#l!P#T#Y#T#U#?U#U;'S#Y;'S;=`#q<%lO#YU#?XVO!O#Y!O!P#l!P#h#Y#h#i#?n#i;'S#Y;'S;=`#q<%lO#YU#?qVOp#Ypq#@Wq!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#YU#@]TjQO!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#YU#@oVO!O#Y!O!P#l!P#U#Y#U#V#AU#V;'S#Y;'S;=`#q<%lO#YU#AXVO!O#Y!O!P#l!P#h#Y#h#i#An#i;'S#Y;'S;=`#q<%lO#YU#AqVO!O#Y!O!P#l!P#T#Y#T#U#BW#U;'S#Y;'S;=`#q<%lO#YU#BZVO!O#Y!O!P#l!P#]#Y#]#^#Bp#^;'S#Y;'S;=`#q<%lO#YU#BsVO!O#Y!O!P#l!P#b#Y#b#c#CY#c;'S#Y;'S;=`#q<%lO#YU#C]VOp#Ypq#Crq!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#YU#CwVtQO!O#Y!O!P#l!P#g#Y#g#h#D^#h;'S#Y;'S;=`#q<%lO#YU#DaVO!O#Y!O!P#l!P#i#Y#i#j#Dv#j;'S#Y;'S;=`#q<%lO#YU#DyVO!O#Y!O!P#l!P#V#Y#V#W#E`#W;'S#Y;'S;=`#q<%lO#YU#EcVO!O#Y!O!P#l!P#[#Y#[#]#Ex#];'S#Y;'S;=`#q<%lO#YU#E{VOp#Ypq#Fbq!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#YU#FeVO!O#Y!O!P#l!P#T#Y#T#U#Fz#U;'S#Y;'S;=`#q<%lO#YU#F}VOp#Ypq#Gdq!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#YU#GiTiQO!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#YU#G{VO!O#Y!O!P#l!P#]#Y#]#^#Hb#^;'S#Y;'S;=`#q<%lO#YU#HeVO!O#Y!O!P#l!P#b#Y#b#c#Hz#c;'S#Y;'S;=`#q<%lO#YU#H}VO!O#Y!O!P#l!P#V#Y#V#W#Id#W;'S#Y;'S;=`#q<%lO#YU#IgVO!O#Y!O!P#l!P#X#Y#X#Y#I|#Y;'S#Y;'S;=`#q<%lO#YU#JPVOp#Ypq#Jfq!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#YU#JiVOx#Yxy#KOy!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#YU#KTT|QO!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#YU#KgVO!O#Y!O!P#l!P#T#Y#T#U#K|#U;'S#Y;'S;=`#q<%lO#YU#LPVO!O#Y!O!P#l!P#_#Y#_#`#Lf#`;'S#Y;'S;=`#q<%lO#YU#LiVO!O#Y!O!P#l!P#X#Y#X#Y#MO#Y;'S#Y;'S;=`#q<%lO#YU#MTT]QO!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#YU#MgVO!O#Y!O!P#l!P#g#Y#g#h#M|#h;'S#Y;'S;=`#q<%lO#YU#NPVO!O#Y!O!P#l!P#X#Y#X#Y#Nf#Y;'S#Y;'S;=`#q<%lO#YU#NiVOp#Ypq$ Oq!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#YU$ TTnQO!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#YU$ gVO!O#Y!O!P#l!P#X#Y#X#Y$ |#Y;'S#Y;'S;=`#q<%lO#YU$!PVOp#Ypq$!fq!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#YU$!i_O!O#Y!O!P#l!P#T#Y#T#U$#h#U#V#Y#V#W$/P#W#b#Y#b#c$;g#c#g#Y#g#h$Du#h#i#Y#i#j%&m#j;'S#Y;'S;=`#q<%lO#YU$#kVO!O#Y!O!P#l!P#f#Y#f#g$$Q#g;'S#Y;'S;=`#q<%lO#YU$$TVO!O#Y!O!P#l!P#Z#Y#Z#[$$j#[;'S#Y;'S;=`#q<%lO#YU$$mVO!O#Y!O!P#l!P#i#Y#i#j$%S#j;'S#Y;'S;=`#q<%lO#YU$%VVO!O#Y!O!P#l!P#X#Y#X#Y$%l#Y;'S#Y;'S;=`#q<%lO#YU$%oVOp#Ypq$&Uq!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#YU$&XVO!O#Y!O!P#l!P#U#Y#U#V$&n#V;'S#Y;'S;=`#q<%lO#YU$&qVO!O#Y!O!P#l!P#m#Y#m#n$'W#n;'S#Y;'S;=`#q<%lO#YU$'ZVOp#Ypq$'pq!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#YU$'sVO!O#Y!O!P#l!P#V#Y#V#W$(Y#W;'S#Y;'S;=`#q<%lO#YU$(]VO!O#Y!O!P#l!P#c#Y#c#d$(r#d;'S#Y;'S;=`#q<%lO#YU$(uVO!O#Y!O!P#l!P#b#Y#b#c$)[#c;'S#Y;'S;=`#q<%lO#YU$)_VO!O#Y!O!P#l!P#h#Y#h#i$)t#i;'S#Y;'S;=`#q<%lO#YU$)wVO!O#Y!O!P#l!P#f#Y#f#g$*^#g;'S#Y;'S;=`#q<%lO#YU$*aVO!O#Y!O!P#l!P#T#Y#T#U$*v#U;'S#Y;'S;=`#q<%lO#YU$*yVO!O#Y!O!P#l!P#W#Y#W#X$+`#X;'S#Y;'S;=`#q<%lO#YU$+cVO!O#Y!O!P#l!P#]#Y#]#^$+x#^;'S#Y;'S;=`#q<%lO#YU$+{VO!O#Y!O!P#l!P#V#Y#V#W$,b#W;'S#Y;'S;=`#q<%lO#YU$,eVO!O#Y!O!P#l!P#h#Y#h#i$,z#i;'S#Y;'S;=`#q<%lO#YU$,}VO!O#Y!O!P#l!P#]#Y#]#^$-d#^;'S#Y;'S;=`#q<%lO#YU$-gVO!O#Y!O!P#l!P#c#Y#c#d$-|#d;'S#Y;'S;=`#q<%lO#YU$.PVO!O#Y!O!P#l!P#b#Y#b#c$.f#c;'S#Y;'S;=`#q<%lO#YU$.iTO!O#Y!O!P$.x!P;'S#Y;'S;=`#q<%lO#YU$/PO`QWSU$/SXO!O#Y!O!P#l!P#`#Y#`#a$/o#a#c#Y#c#d$4u#d;'S#Y;'S;=`#q<%lO#YU$/rVO!O#Y!O!P#l!P#T#Y#T#U$0X#U;'S#Y;'S;=`#q<%lO#YU$0[VO!O#Y!O!P#l!P#]#Y#]#^$0q#^;'S#Y;'S;=`#q<%lO#YU$0tVO!O#Y!O!P#l!P#a#Y#a#b$1Z#b;'S#Y;'S;=`#q<%lO#YU$1^VOp#Ypq$1sq!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#YU$1vVO!O#Y!O!P#l!P#h#Y#h#i$2]#i;'S#Y;'S;=`#q<%lO#YU$2`VO!O#Y!O!P#l!P#[#Y#[#]$2u#];'S#Y;'S;=`#q<%lO#YU$2xVO!O#Y!O!P#l!P#T#Y#T#U$3_#U;'S#Y;'S;=`#q<%lO#YU$3bVO!O#Y!O!P#l!P#h#Y#h#i$3w#i;'S#Y;'S;=`#q<%lO#YU$3zVOp#Ypq$4aq!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#YU$4fTlQO!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#YU$4xVO!O#Y!O!P#l!P#b#Y#b#c$5_#c;'S#Y;'S;=`#q<%lO#YU$5bVO!O#Y!O!P#l!P#V#Y#V#W$5w#W;'S#Y;'S;=`#q<%lO#YU$5zVO!O#Y!O!P#l!P#`#Y#`#a$6a#a;'S#Y;'S;=`#q<%lO#YU$6dVO!O#Y!O!P#l!P#i#Y#i#j$6y#j;'S#Y;'S;=`#q<%lO#YU$6|VO!O#Y!O!P#l!P#W#Y#W#X$7c#X;'S#Y;'S;=`#q<%lO#YU$7fVO!O#Y!O!P#l!P#X#Y#X#Y$7{#Y;'S#Y;'S;=`#q<%lO#YU$8OVOp#Ypq$8eq!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#YU$8hVO!O#Y!O!P#l!P#h#Y#h#i$8}#i;'S#Y;'S;=`#q<%lO#YU$9QVO!O#Y!O!P#l!P#[#Y#[#]$9g#];'S#Y;'S;=`#q<%lO#YU$9jVO!O#Y!O!P#l!P#T#Y#T#U$:P#U;'S#Y;'S;=`#q<%lO#YU$:SVO!O#Y!O!P#l!P#h#Y#h#i$:i#i;'S#Y;'S;=`#q<%lO#YU$:lVOp#Ypq$;Rq!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#YU$;WTeQO!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#YU$;jVO!O#Y!O!P#l!P#X#Y#X#Y$<P#Y;'S#Y;'S;=`#q<%lO#YU$<SVO!O#Y!O!P#l!P#X#Y#X#Y$<i#Y;'S#Y;'S;=`#q<%lO#YU$<lVO!O#Y!O!P#l!P#W#Y#W#X$=R#X;'S#Y;'S;=`#q<%lO#YU$=UVOp#Ypq$=kq!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#YU$=nVO!O#Y!O!P#l!P#h#Y#h#i$>T#i;'S#Y;'S;=`#q<%lO#YU$>WVO!O#Y!O!P#l!P#c#Y#c#d$>m#d;'S#Y;'S;=`#q<%lO#YU$>pVOp#Ypq$?Vq!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#YU$?YVO!O#Y!O!P#l!P#g#Y#g#h$?o#h;'S#Y;'S;=`#q<%lO#YU$?rVO!O#Y!O!P#l!P#[#Y#[#]$@X#];'S#Y;'S;=`#q<%lO#YU$@[VO!O#Y!O!P#l!P#c#Y#c#d$@q#d;'S#Y;'S;=`#q<%lO#YU$@tVO!O#Y!O!P#l!P#k#Y#k#l$AZ#l;'S#Y;'S;=`#q<%lO#YU$A^VOp#Ypq$Asq!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#YU$AvVO!O#Y!O!P#l!P#h#Y#h#i$B]#i;'S#Y;'S;=`#q<%lO#YU$B`VO!O#Y!O!P#l!P#[#Y#[#]$Bu#];'S#Y;'S;=`#q<%lO#YU$BxVO!O#Y!O!P#l!P#T#Y#T#U$C_#U;'S#Y;'S;=`#q<%lO#YU$CbVO!O#Y!O!P#l!P#h#Y#h#i$Cw#i;'S#Y;'S;=`#q<%lO#YU$CzVOp#Ypq$Daq!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#YU$DfTdQO!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#YU$DxVO!O#Y!O!P#l!P#[#Y#[#]$E_#];'S#Y;'S;=`#q<%lO#YU$EbVO!O#Y!O!P#l!P#c#Y#c#d$Ew#d;'S#Y;'S;=`#q<%lO#YU$EzVO!O#Y!O!P#l!P#k#Y#k#l$Fa#l;'S#Y;'S;=`#q<%lO#YU$FdVOp#Ypq$Fyq!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#YU$F|VO!O#Y!O!P#l!P#U#Y#U#V$Gc#V;'S#Y;'S;=`#q<%lO#YU$GfVO!O#Y!O!P#l!P#c#Y#c#d$G{#d;'S#Y;'S;=`#q<%lO#YU$HOVO!O#Y!O!P#l!P#h#Y#h#i$He#i;'S#Y;'S;=`#q<%lO#YU$HhVO!O#Y!O!P#l!P#[#Y#[#]$H}#];'S#Y;'S;=`#q<%lO#YU$IQVOp#Ypq$Igq!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#YU$IjXO!O#Y!O!P#l!P#W#Y#W#X$JV#X#g#Y#g#h% b#h;'S#Y;'S;=`#q<%lO#YU$JYVO!O#Y!O!P#l!P#]#Y#]#^$Jo#^;'S#Y;'S;=`#q<%lO#YU$JrVO!O#Y!O!P#l!P#f#Y#f#g$KX#g;'S#Y;'S;=`#q<%lO#YU$K[VO!O#Y!O!P#l!P#X#Y#X#Y$Kq#Y;'S#Y;'S;=`#q<%lO#YU$KtVO!O#Y!O!P#l!P#V#Y#V#W$LZ#W;'S#Y;'S;=`#q<%lO#YU$L^VO!O#Y!O!P#l!P#h#Y#h#i$Ls#i;'S#Y;'S;=`#q<%lO#YU$LvVO!O#Y!O!P#l!P#]#Y#]#^$M]#^;'S#Y;'S;=`#q<%lO#YU$M`VO!O#Y!O!P#l!P#c#Y#c#d$Mu#d;'S#Y;'S;=`#q<%lO#YU$MxVO!O#Y!O!P#l!P#b#Y#b#c$N_#c;'S#Y;'S;=`#q<%lO#YU$NbVO!O#Y!O!P#l!P#g#Y#g#h$Nw#h;'S#Y;'S;=`#q<%lO#YU$NzTO!O#Y!O!P% Z!P;'S#Y;'S;=`#q<%lO#YU% bOcQWSU% eVO!O#Y!O!P#l!P#h#Y#h#i% z#i;'S#Y;'S;=`#q<%lO#YU% }VO!O#Y!O!P#l!P#T#Y#T#U%!d#U;'S#Y;'S;=`#q<%lO#YU%!gVO!O#Y!O!P#l!P#h#Y#h#i%!|#i;'S#Y;'S;=`#q<%lO#YU%#PVO!O#Y!O!P#l!P#X#Y#X#Y%#f#Y;'S#Y;'S;=`#q<%lO#YU%#iVO!O#Y!O!P#l!P#a#Y#a#b%$O#b;'S#Y;'S;=`#q<%lO#YU%$RVO!O#Y!O!P#l!P#X#Y#X#Y%$h#Y;'S#Y;'S;=`#q<%lO#YU%$kVO!O#Y!O!P#l!P#b#Y#b#c%%Q#c;'S#Y;'S;=`#q<%lO#YU%%TVO!O#Y!O!P#l!P#h#Y#h#i%%j#i;'S#Y;'S;=`#q<%lO#YU%%mVO!O#Y!O!P#l!P#g#Y#g#h%&S#h;'S#Y;'S;=`#q<%lO#YU%&VTO!O#Y!O!P%&f!P;'S#Y;'S;=`#q<%lO#YU%&mObQWSU%&pVO!O#Y!O!P#l!P#g#Y#g#h%'V#h;'S#Y;'S;=`#q<%lO#YU%'YVO!O#Y!O!P#l!P#X#Y#X#Y%'o#Y;'S#Y;'S;=`#q<%lO#YU%'rVOp#Ypq%(Xq!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#YU%([VO!O#Y!O!P#l!P#]#Y#]#^%(q#^;'S#Y;'S;=`#q<%lO#YU%(tVO!O#Y!O!P#l!P#b#Y#b#c%)Z#c;'S#Y;'S;=`#q<%lO#YU%)^VO!O#Y!O!P#l!P#W#Y#W#X%)s#X;'S#Y;'S;=`#q<%lO#YU%)vVO!O#Y!O!P#l!P#i#Y#i#j%*]#j;'S#Y;'S;=`#q<%lO#YU%*`VO!O#Y!O!P#l!P#V#Y#V#W%*u#W;'S#Y;'S;=`#q<%lO#YU%*xVO!O#Y!O!P#l!P#h#Y#h#i%+_#i;'S#Y;'S;=`#q<%lO#YU%+bVO!O#Y!O!P#l!P#]#Y#]#^%+w#^;'S#Y;'S;=`#q<%lO#YU%+zVO!O#Y!O!P#l!P#c#Y#c#d%,a#d;'S#Y;'S;=`#q<%lO#YU%,dVO!O#Y!O!P#l!P#b#Y#b#c%,y#c;'S#Y;'S;=`#q<%lO#YU%,|VOp#Ypq%-cq!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#YU%-fVO!O#Y!O!P#l!P#c#Y#c#d%-{#d;'S#Y;'S;=`#q<%lO#YU%.OVO!O#Y!O!P#l!P#b#Y#b#c%.e#c;'S#Y;'S;=`#q<%lO#YU%.hVOp#Ypq%.}q!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#YU%/STmQO!O#Y!O!P#l!P;'S#Y;'S;=`#q<%lO#Y",
  tokenizers: [TakeInput, 1, 2, 3, 4, new LocalTokenGroup("k~RP!O!PU~XSXYeYZe]^epqe~jOV~~", 26, 6)],
  topRules: { "Program": [0, 3] },
  tokenPrec: 0
});

// parser-debug-tool.mjs
var import_fs = require("fs");
function printJSON(input) {
  console.log(JSON.stringify(parser.parse(input), null, 2));
}
var fileContents = (0, import_fs.readFileSync)("input.txt", "utf8");
console.log("File contents:");
console.log(fileContents);
console.log("JSON");
printJSON(fileContents);
