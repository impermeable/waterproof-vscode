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
  /// Create a new node prop type.
  constructor(config = {}) {
    this.id = nextPropID++;
    this.perNode = !!config.perNode;
    this.deserialize = config.deserialize || (() => {
      throw new Error("This node type doesn't define a deserialize function");
    });
  }
  /// This is meant to be used with
  /// [`NodeSet.extend`](#common.NodeSet.extend) or
  /// [`LRParser.configure`](#lr.ParserConfig.props) to compute
  /// prop values for each node type in the set. Takes a [match
  /// object](#common.NodeType^match) or function that returns undefined
  /// if the node type doesn't get this prop, and the prop's value if
  /// it does.
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
NodeProp.contextHash = new NodeProp({ perNode: true });
NodeProp.lookAhead = new NodeProp({ perNode: true });
NodeProp.mounted = new NodeProp({ perNode: true });
var noProps = /* @__PURE__ */ Object.create(null);
var NodeType = class {
  /// @internal
  constructor(name, props, id, flags = 0) {
    this.name = name;
    this.props = props;
    this.id = id;
    this.flags = flags;
  }
  /// Define a node type.
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
  /// Retrieves a node prop for this type. Will return `undefined` if
  /// the prop isn't present on this node.
  prop(prop) {
    return this.props[prop.id];
  }
  /// True when this is the top node of a grammar.
  get isTop() {
    return (this.flags & 1) > 0;
  }
  /// True when this node is produced by a skip rule.
  get isSkipped() {
    return (this.flags & 2) > 0;
  }
  /// Indicates whether this is an error node.
  get isError() {
    return (this.flags & 4) > 0;
  }
  /// When true, this node type doesn't correspond to a user-declared
  /// named node, for example because it is used to cache repetition.
  get isAnonymous() {
    return (this.flags & 8) > 0;
  }
  /// Returns true when this node's name or one of its
  /// [groups](#common.NodeProp^group) matches the given string.
  is(name) {
    if (typeof name == "string") {
      if (this.name == name)
        return true;
      let group = this.prop(NodeProp.group);
      return group ? group.indexOf(name) > -1 : false;
    }
    return this.id == name;
  }
  /// Create a function from node types to arbitrary values by
  /// specifying an object whose property names are node or
  /// [group](#common.NodeProp^group) names. Often useful with
  /// [`NodeProp.add`](#common.NodeProp.add). You can put multiple
  /// names, separated by spaces, in a single property name to map
  /// multiple node names to a single value.
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
  /// Create a set with the given types. The `id` property of each
  /// type should correspond to its position within the array.
  constructor(types) {
    this.types = types;
    for (let i = 0; i < types.length; i++)
      if (types[i].id != i)
        throw new RangeError("Node type ids should correspond to array positions when creating a node set");
  }
  /// Create a copy of this set with some node properties added. The
  /// arguments to this method can be created with
  /// [`NodeProp.add`](#common.NodeProp.add).
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
  /// Construct a new tree. See also [`Tree.build`](#common.Tree^build).
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
  /// @internal
  toString() {
    let mounted = this.prop(NodeProp.mounted);
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
  /// Get a [tree cursor](#common.TreeCursor) positioned at the top of
  /// the tree. Mode can be used to [control](#common.IterMode) which
  /// nodes the cursor visits.
  cursor(mode = 0) {
    return new TreeCursor(this.topNode, mode);
  }
  /// Get a [tree cursor](#common.TreeCursor) pointing into this tree
  /// at the given position and side (see
  /// [`moveTo`](#common.TreeCursor.moveTo).
  cursorAt(pos, side = 0, mode = 0) {
    let scope = CachedNode.get(this) || this.topNode;
    let cursor = new TreeCursor(scope);
    cursor.moveTo(pos, side);
    CachedNode.set(this, cursor._tree);
    return cursor;
  }
  /// Get a [syntax node](#common.SyntaxNode) object for the top of the
  /// tree.
  get topNode() {
    return new TreeNode(this, 0, 0, null);
  }
  /// Get the [syntax node](#common.SyntaxNode) at the given position.
  /// If `side` is -1, this will move into nodes that end at the
  /// position. If 1, it'll move into nodes that start at the
  /// position. With 0, it'll only enter nodes that cover the position
  /// from both sides.
  ///
  /// Note that this will not enter
  /// [overlays](#common.MountedTree.overlay), and you often want
  /// [`resolveInner`](#common.Tree.resolveInner) instead.
  resolve(pos, side = 0) {
    let node = resolveNode(CachedNode.get(this) || this.topNode, pos, side, false);
    CachedNode.set(this, node);
    return node;
  }
  /// Like [`resolve`](#common.Tree.resolve), but will enter
  /// [overlaid](#common.MountedTree.overlay) nodes, producing a syntax node
  /// pointing into the innermost overlaid tree at the given position
  /// (with parent links going through all parent structure, including
  /// the host trees).
  resolveInner(pos, side = 0) {
    let node = resolveNode(CachedInnerNode.get(this) || this.topNode, pos, side, true);
    CachedInnerNode.set(this, node);
    return node;
  }
  /// Iterate over the tree and its children, calling `enter` for any
  /// node that touches the `from`/`to` region (if given) before
  /// running over such a node's children, and `leave` (if given) when
  /// leaving the node. When `enter` returns `false`, that node will
  /// not have its children iterated over (or `leave` called).
  iterate(spec) {
    let { enter, leave, from = 0, to = this.length } = spec;
    for (let c = this.cursor((spec.mode || 0) | IterMode.IncludeAnonymous); ; ) {
      let entered = false;
      if (c.from <= to && c.to >= from && (c.type.isAnonymous || enter(c) !== false)) {
        if (c.firstChild())
          continue;
        entered = true;
      }
      for (; ; ) {
        if (entered && leave && !c.type.isAnonymous)
          leave(c);
        if (c.nextSibling())
          break;
        if (!c.parent())
          return;
        entered = true;
      }
    }
  }
  /// Get the value of the given [node prop](#common.NodeProp) for this
  /// node. Works with both per-node and per-type props.
  prop(prop) {
    return !prop.perNode ? this.type.prop(prop) : this.props ? this.props[prop.id] : void 0;
  }
  /// Returns the node's [per-node props](#common.NodeProp.perNode) in a
  /// format that can be passed to the [`Tree`](#common.Tree)
  /// constructor.
  get propValues() {
    let result = [];
    if (this.props)
      for (let id in this.props)
        result.push([+id, this.props[id]]);
    return result;
  }
  /// Balance the direct children of this tree, producing a copy of
  /// which may have children grouped into subtrees with type
  /// [`NodeType.none`](#common.NodeType^none).
  balance(config = {}) {
    return this.children.length <= 8 ? this : balanceRange(NodeType.none, this.children, this.positions, 0, this.children.length, 0, this.length, (children, positions, length) => new Tree(this.type, children, positions, length, this.propValues), config.makeTree || ((children, positions, length) => new Tree(NodeType.none, children, positions, length)));
  }
  /// Build a tree from a postfix-ordered buffer of node information,
  /// or a cursor over such a buffer.
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
  /// Create a tree buffer.
  constructor(buffer, length, set) {
    this.buffer = buffer;
    this.length = length;
    this.set = set;
  }
  /// @internal
  get type() {
    return NodeType.none;
  }
  /// @internal
  toString() {
    let result = [];
    for (let index = 0; index < this.buffer.length; ) {
      result.push(this.childString(index));
      index = this.buffer[index + 3];
    }
    return result.join(",");
  }
  /// @internal
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
  /// @internal
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
  /// @internal
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
function enterUnfinishedNodesBefore(node, pos) {
  let scan = node.childBefore(pos);
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
var TreeNode = class {
  constructor(_tree, from, index, _parent) {
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
          if (!(mode & IterMode.IgnoreMounts) && next.props && (mounted = next.prop(NodeProp.mounted)) && !mounted.overlay)
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
    if (!(mode & IterMode.IgnoreOverlays) && (mounted = this._tree.prop(NodeProp.mounted)) && mounted.overlay) {
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
  cursor(mode = 0) {
    return new TreeCursor(this, mode);
  }
  get tree() {
    return this._tree;
  }
  toTree() {
    return this._tree;
  }
  resolve(pos, side = 0) {
    return resolveNode(this, pos, side, false);
  }
  resolveInner(pos, side = 0) {
    return resolveNode(this, pos, side, true);
  }
  enterUnfinishedNodesBefore(pos) {
    return enterUnfinishedNodesBefore(this, pos);
  }
  getChild(type, before = null, after = null) {
    let r = getChildren(this, type, before, after);
    return r.length ? r[0] : null;
  }
  getChildren(type, before = null, after = null) {
    return getChildren(this, type, before, after);
  }
  /// @internal
  toString() {
    return this._tree.toString();
  }
  get node() {
    return this;
  }
  matchContext(context) {
    return matchNodeContext(this, context);
  }
};
function getChildren(node, type, before, after) {
  let cur = node.cursor(), result = [];
  if (!cur.firstChild())
    return result;
  if (before != null) {
    while (!cur.type.is(before))
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
  for (let p = node.parent; i >= 0; p = p.parent) {
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
var BufferNode = class {
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
  cursor(mode = 0) {
    return new TreeCursor(this, mode);
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
  resolve(pos, side = 0) {
    return resolveNode(this, pos, side, false);
  }
  resolveInner(pos, side = 0) {
    return resolveNode(this, pos, side, true);
  }
  enterUnfinishedNodesBefore(pos) {
    return enterUnfinishedNodesBefore(this, pos);
  }
  /// @internal
  toString() {
    return this.context.buffer.childString(this.index);
  }
  getChild(type, before = null, after = null) {
    let r = getChildren(this, type, before, after);
    return r.length ? r[0] : null;
  }
  getChildren(type, before = null, after = null) {
    return getChildren(this, type, before, after);
  }
  get node() {
    return this;
  }
  matchContext(context) {
    return matchNodeContext(this, context);
  }
};
var TreeCursor = class {
  /// Shorthand for `.type.name`.
  get name() {
    return this.type.name;
  }
  /// @internal
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
  /// @internal
  toString() {
    return this.buffer ? this.buffer.buffer.childString(this.index) : this._tree.toString();
  }
  /// @internal
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
  /// Move the cursor to this node's first child. When this returns
  /// false, the node has no child, and the cursor has not been moved.
  firstChild() {
    return this.enterChild(
      1,
      0,
      4
      /* Side.DontCare */
    );
  }
  /// Move the cursor to this node's last child.
  lastChild() {
    return this.enterChild(
      -1,
      0,
      4
      /* Side.DontCare */
    );
  }
  /// Move the cursor to the first child that ends after `pos`.
  childAfter(pos) {
    return this.enterChild(
      1,
      pos,
      2
      /* Side.After */
    );
  }
  /// Move to the last child that starts before `pos`.
  childBefore(pos) {
    return this.enterChild(
      -1,
      pos,
      -2
      /* Side.Before */
    );
  }
  /// Move the cursor to the child around `pos`. If side is -1 the
  /// child may end at that position, when 1 it may start there. This
  /// will also enter [overlaid](#common.MountedTree.overlay)
  /// [mounted](#common.NodeProp^mounted) trees unless `overlays` is
  /// set to false.
  enter(pos, side, mode = this.mode) {
    if (!this.buffer)
      return this.yield(this._tree.enter(pos, side, mode));
    return mode & IterMode.ExcludeBuffers ? false : this.enterChild(1, pos, side);
  }
  /// Move to the node's parent node, if this isn't the top node.
  parent() {
    if (!this.buffer)
      return this.yieldNode(this.mode & IterMode.IncludeAnonymous ? this._tree._parent : this._tree.parent);
    if (this.stack.length)
      return this.yieldBuf(this.stack.pop());
    let parent = this.mode & IterMode.IncludeAnonymous ? this.buffer.parent : this.buffer.parent.nextSignificantParent();
    this.buffer = null;
    return this.yieldNode(parent);
  }
  /// @internal
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
  /// Move to this node's next sibling, if any.
  nextSibling() {
    return this.sibling(1);
  }
  /// Move to this node's previous sibling, if any.
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
  /// Move to the next node in a
  /// [pre-order](https://en.wikipedia.org/wiki/Tree_traversal#Pre-order,_NLR)
  /// traversal, going from a node to its first child or, if the
  /// current node is empty or `enter` is false, its next sibling or
  /// the next sibling of the first parent node that has one.
  next(enter = true) {
    return this.move(1, enter);
  }
  /// Move to the next node in a last-to-first pre-order traveral. A
  /// node is followed by its last child or, if it has none, its
  /// previous sibling or the previous sibling of the first parent
  /// node that has one.
  prev(enter = true) {
    return this.move(-1, enter);
  }
  /// Move the cursor to the innermost node that covers `pos`. If
  /// `side` is -1, it will enter nodes that end at `pos`. If it is 1,
  /// it will enter nodes that start at `pos`.
  moveTo(pos, side = 0) {
    while (this.from == this.to || (side < 1 ? this.from >= pos : this.from > pos) || (side > -1 ? this.to <= pos : this.to < pos))
      if (!this.parent())
        break;
    while (this.enterChild(1, pos, side)) {
    }
    return this;
  }
  /// Get a [syntax node](#common.SyntaxNode) at the cursor's current
  /// position.
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
  /// Get the [tree](#common.Tree) that represents the current node, if
  /// any. Will return null when the node is in a [tree
  /// buffer](#common.TreeBuffer).
  get tree() {
    return this.buffer ? null : this._tree._tree;
  }
  /// Iterate over the current node and all its descendants, calling
  /// `enter` when entering a node and `leave`, if given, when leaving
  /// one. When `enter` returns `false`, any children of that node are
  /// skipped, and `leave` isn't called for it.
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
        if (this.nextSibling())
          break;
        if (!depth)
          return;
        this.parent();
        depth--;
        mustLeave = true;
      }
    }
  }
  /// Test whether the current node matches a given context—a sequence
  /// of direct parent node names. Empty strings in the context array
  /// are treated as wildcards.
  matchContext(context) {
    if (!this.buffer)
      return matchNodeContext(this.node, context);
    let { buffer } = this.buffer, { types } = buffer.set;
    for (let i = context.length - 1, d = this.stack.length - 1; i >= 0; d--) {
      if (d < 0)
        return matchNodeContext(this.node, context, i);
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
  function takeNode(parentStart, minPos, children2, positions2, inRepeat) {
    let { id, start, end, size } = cursor;
    let lookAheadAtStart = lookAhead;
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
            makeRepeatLeaf(localChildren, localPositions, start, lastGroup, cursor.end, lastEnd, localInRepeat, lookAheadAtStart);
            lastGroup = localChildren.length;
            lastEnd = cursor.end;
          }
          cursor.next();
        } else {
          takeNode(start, endPos, localChildren, localPositions, localInRepeat);
        }
      }
      if (localInRepeat >= 0 && lastGroup > 0 && lastGroup < localChildren.length)
        makeRepeatLeaf(localChildren, localPositions, start, lastGroup, start, lastEnd, localInRepeat, lookAheadAtStart);
      localChildren.reverse();
      localPositions.reverse();
      if (localInRepeat > -1 && lastGroup > 0) {
        let make = makeBalanced(type);
        node = balanceRange(type, localChildren, localPositions, 0, localChildren.length, 0, end - start, make, make);
      } else {
        node = makeTree(type, localChildren, localPositions, end - start, lookAheadAtStart - end);
      }
    }
    children2.push(node);
    positions2.push(startPos);
  }
  function makeBalanced(type) {
    return (children2, positions2, length2) => {
      let lookAhead2 = 0, lastI = children2.length - 1, last, lookAheadProp;
      if (lastI >= 0 && (last = children2[lastI]) instanceof Tree) {
        if (!lastI && last.type == type && last.length == length2)
          return last;
        if (lookAheadProp = last.prop(NodeProp.lookAhead))
          lookAhead2 = positions2[lastI] + last.length + lookAheadProp;
      }
      return makeTree(type, children2, positions2, length2, lookAhead2);
    };
  }
  function makeRepeatLeaf(children2, positions2, base, i, from, to, type, lookAhead2) {
    let localChildren = [], localPositions = [];
    while (children2.length > i) {
      localChildren.push(children2.pop());
      localPositions.push(positions2.pop() + base - from);
    }
    children2.push(makeTree(nodeSet.types[type], localChildren, localPositions, to - from, lookAhead2 - to));
    positions2.push(from - base);
  }
  function makeTree(type, children2, positions2, length2, lookAhead2 = 0, props) {
    if (contextHash) {
      let pair2 = [NodeProp.contextHash, contextHash];
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
    takeNode(data.start || 0, data.bufferStart || 0, children, positions, -1);
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
  /// Start a parse, returning a [partial parse](#common.PartialParse)
  /// object. [`fragments`](#common.TreeFragment) can be passed in to
  /// make the parse incremental.
  ///
  /// By default, the entire input is parsed. You can pass `ranges`,
  /// which should be a sorted array of non-empty, non-overlapping
  /// ranges, to parse only those ranges. The tree returned in that
  /// case will start at `ranges[0].from`.
  startParse(input, fragments, ranges) {
    if (typeof input == "string")
      input = new StringInput(input);
    ranges = !ranges ? [new Range(0, input.length)] : ranges.length ? ranges.map((r) => new Range(r.from, r.to)) : [new Range(0, 0)];
    return this.createParse(input, fragments || [], ranges);
  }
  /// Run a full parse, returning the resulting tree.
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
  /// @internal
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
  /// @internal
  toString() {
    return `[${this.stack.filter((_, i) => i % 3 == 0).concat(this.state)}]@${this.pos}${this.score ? "!" + this.score : ""}`;
  }
  // Start an empty stack
  /// @internal
  static start(p, state, pos = 0) {
    let cx = p.parser.context;
    return new Stack(p, [], state, pos, pos, 0, [], 0, cx ? new StackContext(cx, cx.start) : null, 0, null);
  }
  /// The stack's current [context](#lr.ContextTracker) value, if
  /// any. Its type will depend on the context tracker's type
  /// parameter, or it will be `null` if there is no context
  /// tracker.
  get context() {
    return this.curContext ? this.curContext.context : null;
  }
  // Push a state onto the stack, tracking its start position as well
  // as the buffer base at that point.
  /// @internal
  pushState(state, start) {
    this.stack.push(this.state, start, this.bufferBase + this.buffer.length);
    this.state = state;
  }
  // Apply a reduce action
  /// @internal
  reduce(action) {
    var _a;
    let depth = action >> 19, type = action & 65535;
    let { parser: parser2 } = this.p;
    let dPrec = parser2.dynamicPrecedence(type);
    if (dPrec)
      this.score += dPrec;
    if (depth == 0) {
      this.pushState(parser2.getGoto(this.state, type, true), this.reducePos);
      if (type < parser2.minRepeatTerm)
        this.storeNode(type, this.reducePos, this.reducePos, 4, true);
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
  /// @internal
  storeNode(term, start, end, size = 4, isReduce = false) {
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
    if (!isReduce || this.pos == end) {
      this.buffer.push(term, start, end, size);
    } else {
      let index = this.buffer.length;
      if (index > 0 && this.buffer[index - 4] != 0)
        while (index > 0 && this.buffer[index - 2] > end) {
          this.buffer[index] = this.buffer[index - 4];
          this.buffer[index + 1] = this.buffer[index - 3];
          this.buffer[index + 2] = this.buffer[index - 2];
          this.buffer[index + 3] = this.buffer[index - 1];
          index -= 4;
          if (size > 4)
            size -= 4;
        }
      this.buffer[index] = term;
      this.buffer[index + 1] = start;
      this.buffer[index + 2] = end;
      this.buffer[index + 3] = size;
    }
  }
  // Apply a shift action
  /// @internal
  shift(action, next, nextEnd) {
    let start = this.pos;
    if (action & 131072) {
      this.pushState(action & 65535, this.pos);
    } else if ((action & 262144) == 0) {
      let nextState = action, { parser: parser2 } = this.p;
      if (nextEnd > this.pos || next <= parser2.maxNode) {
        this.pos = nextEnd;
        if (!parser2.stateFlag(
          nextState,
          1
          /* StateFlag.Skipped */
        ))
          this.reducePos = nextEnd;
      }
      this.pushState(nextState, start);
      this.shiftContext(next, start);
      if (next <= parser2.maxNode)
        this.buffer.push(next, start, nextEnd, 4);
    } else {
      this.pos = nextEnd;
      this.shiftContext(next, start);
      if (next <= this.p.parser.maxNode)
        this.buffer.push(next, start, nextEnd, 4);
    }
  }
  // Apply an action
  /// @internal
  apply(action, next, nextEnd) {
    if (action & 65536)
      this.reduce(action);
    else
      this.shift(action, next, nextEnd);
  }
  // Add a prebuilt (reused) node into the buffer.
  /// @internal
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
  /// @internal
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
  /// @internal
  recoverByDelete(next, nextEnd) {
    let isNode = next <= this.p.parser.maxNode;
    if (isNode)
      this.storeNode(next, this.pos, nextEnd, 4);
    this.storeNode(0, this.pos, nextEnd, isNode ? 8 : 4);
    this.pos = this.reducePos = nextEnd;
    this.score -= 190;
  }
  /// Check if the given term would be able to be shifted (optionally
  /// after some reductions) on this stack. This can be useful for
  /// external tokenizers that want to make sure they only provide a
  /// given token when it applies.
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
  /// @internal
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
      stack.score -= 200;
      result.push(stack);
    }
    return result;
  }
  // Force a reduce, if possible. Return false if that can't
  // be done.
  /// @internal
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
      this.storeNode(0, this.reducePos, this.reducePos, 4, true);
      this.score -= 100;
    }
    this.reducePos = this.pos;
    this.reduce(reduce);
    return true;
  }
  /// Try to scan through the automaton to find some kind of reduction
  /// that can be applied. Used when the regular ForcedReduce field
  /// isn't a valid action. @internal
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
  /// @internal
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
  /// Check whether this state has no further actions (assumed to be a direct descendant of the
  /// top state, since any other states must be able to continue
  /// somehow). @internal
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
  /// Restart the stack (put it back in its start state). Only safe
  /// when this.stack.length == 3 (state is directly below the top
  /// state). @internal
  restart() {
    this.state = this.stack[0];
    this.stack.length = 0;
  }
  /// @internal
  sameState(other) {
    if (this.state != other.state || this.stack.length != other.stack.length)
      return false;
    for (let i = 0; i < this.stack.length; i += 3)
      if (this.stack[i] != other.stack[i])
        return false;
    return true;
  }
  /// Get the parser used by this stack.
  get parser() {
    return this.p.parser;
  }
  /// Test whether a given dialect (by numeric ID, as exported from
  /// the terms file) is enabled.
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
  /// @internal
  emitContext() {
    let last = this.buffer.length - 1;
    if (last < 0 || this.buffer[last] != -3)
      this.buffer.push(this.curContext.hash, this.pos, this.pos, -3);
  }
  /// @internal
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
  /// @internal
  setLookAhead(lookAhead) {
    if (lookAhead > this.lookAhead) {
      this.emitLookAhead();
      this.lookAhead = lookAhead;
    }
  }
  /// @internal
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
var Recover;
(function(Recover2) {
  Recover2[Recover2["Insert"] = 200] = "Insert";
  Recover2[Recover2["Delete"] = 190] = "Delete";
  Recover2[Recover2["Reduce"] = 100] = "Reduce";
  Recover2[Recover2["MaxNext"] = 4] = "MaxNext";
  Recover2[Recover2["MaxInsertStackDepth"] = 300] = "MaxInsertStackDepth";
  Recover2[Recover2["DampenInsertStackDepth"] = 120] = "DampenInsertStackDepth";
  Recover2[Recover2["MinBigReduction"] = 2e3] = "MinBigReduction";
})(Recover || (Recover = {}));
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
  /// @internal
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
  /// @internal
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
  /// @internal
  clipPos(pos) {
    if (pos >= this.range.from && pos < this.range.to)
      return pos;
    for (let range of this.ranges)
      if (range.to > pos)
        return Math.max(pos, range.from);
    return this.end;
  }
  /// Look at a code unit near the stream position. `.peek(0)` equals
  /// `.next`, `.peek(-1)` gives you the previous character, and so
  /// on.
  ///
  /// Note that looking around during tokenizing creates dependencies
  /// on potentially far-away content, which may reduce the
  /// effectiveness incremental parsing—when looking forward—or even
  /// cause invalid reparses when looking backward more than 25 code
  /// units, since the library does not track lookbehind.
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
  /// Accept a token. By default, the end of the token is set to the
  /// current stream position, but you can pass an offset (relative to
  /// the stream position) to change that.
  acceptToken(token, endOffset = 0) {
    let end = endOffset ? this.resolveOffset(endOffset, -1) : this.pos;
    if (end == null || end < this.token.start)
      throw new RangeError("Token end out of bounds");
    this.token.value = token;
    this.token.end = end;
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
  /// Move the stream forward N (defaults to 1) code units. Returns
  /// the new value of [`next`](#lr.InputStream.next).
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
  /// @internal
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
  /// @internal
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
      readToken(this.data, input, stack, 0, this.data, this.precTable);
      if (input.token.value > -1)
        break;
      if (this.elseToken == null)
        return;
      if (input.next < 0)
        break;
      input.advance();
      input.reset(input.pos, input.token);
      skipped++;
    }
    if (skipped) {
      input.reset(start, input.token);
      input.acceptToken(this.elseToken, skipped);
    }
  }
};
LocalTokenGroup.prototype.contextual = TokenGroup.prototype.fallback = TokenGroup.prototype.extend = false;
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
      if (input.next < 0 && high > low && data[accEnd + high * 3 - 3] == 65535 && data[accEnd + high * 3 - 3] == 65535) {
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
var Safety;
(function(Safety2) {
  Safety2[Safety2["Margin"] = 25] = "Margin";
})(Safety || (Safety = {}));
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
            /* Safety.Margin */
          )) : Math.min(tree.length, Math.max(
            cursor.from + 1,
            pos + 25
            /* Safety.Margin */
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
var Rec;
(function(Rec2) {
  Rec2[Rec2["Distance"] = 5] = "Distance";
  Rec2[Rec2["MaxRemainingPerStep"] = 3] = "MaxRemainingPerStep";
  Rec2[Rec2["MinBufferLengthPrune"] = 500] = "MinBufferLengthPrune";
  Rec2[Rec2["ForceReduceLimit"] = 10] = "ForceReduceLimit";
  Rec2[Rec2["CutDepth"] = 15e3] = "CutDepth";
  Rec2[Rec2["CutTo"] = 9e3] = "CutTo";
  Rec2[Rec2["MaxLeftAssociativeReductionCount"] = 300] = "MaxLeftAssociativeReductionCount";
  Rec2[Rec2["MaxStackCount"] = 12] = "MaxStackCount";
})(Rec || (Rec = {}));
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
      if (finished)
        return this.stackToTree(finished);
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
      if (finished)
        return this.stackToTree(finished.forceAll());
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
    if (stack.stack.length >= 15e3) {
      while (stack.stack.length > 9e3 && stack.forceReduce()) {
      }
    }
    let actions = this.tokens.getActions(stack);
    for (let i = 0; i < actions.length; ) {
      let action = actions[i++], term = actions[i++], end = actions[i++];
      let last = i == actions.length || !split;
      let localStack = last ? stack : stack.split();
      localStack.apply(action, term, end);
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
  /// @internal
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
  /// Get a goto table entry @internal
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
  /// Check if this state has an action for a given terminal @internal
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
  /// @internal
  stateSlot(state, slot) {
    return this.states[state * 6 + slot];
  }
  /// @internal
  stateFlag(state, flag) {
    return (this.stateSlot(
      state,
      0
      /* ParseState.Flags */
    ) & flag) > 0;
  }
  /// @internal
  validAction(state, action) {
    return !!this.allActions(state, (a) => a == action ? true : null);
  }
  /// @internal
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
  /// Get the states that can follow this one through shift actions or
  /// goto jumps. @internal
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
  /// Configure the parser. Returns a new parser instance that has the
  /// given settings modified. Settings not provided in `config` are
  /// kept from the original parser.
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
  /// Tells you whether any [parse wrappers](#lr.ParserConfig.wrap)
  /// are registered for this parser.
  hasWrappers() {
    return this.wrappers.length > 0;
  }
  /// Returns the name associated with a given term. This will only
  /// work for all terms when the parser was generated with the
  /// `--names` option. By default, only the names of tagged terms are
  /// stored.
  getName(term) {
    return this.termNames ? this.termNames[term] : String(term <= this.maxNode && this.nodeSet.types[term].name || term);
  }
  /// The eof term id is always allocated directly after the node
  /// types. @internal
  get eofTerm() {
    return this.maxNode + 1;
  }
  /// The type of top node produced by the parser.
  get topNode() {
    return this.nodeSet.types[this.top[1]];
  }
  /// @internal
  dynamicPrecedence(term) {
    let prec = this.dynamicPrecedences;
    return prec == null ? 0 : prec[term] || 0;
  }
  /// @internal
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
  /// Used by the output of the parser generator. Not available to
  /// user code. @hide
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

// syntax.js
var parser = LRParser.deserialize({
  version: 14,
  states: "(pQYQPOOOOQO'#C`'#C`O!sO`O'#C`O!xO`O'#C`O!}O`O'#C`O#SO`O'#C`O#XO`O'#C`O#^O`O'#C`O#cO`O'#C`O#hO`O'#C`O#mO`O'#C`O#rO`O'#C`O#wO`O'#C`O#|QQO'#C_OOQO'#Cd'#CdQYQPOOO$ROSO,58zO$WO`O,58zO$]OSO,58zO$bOSO,58zO$gOSO,58zO$lOPO,58zO$wOSO,58zO$|OWO,58zO%ROSO,58zO%^OPO,58zO%cOPO,58zOOQO,58y,58yOOQO-E6b-E6bO%hO`O1G.fOOQO1G.f1G.fO%mO`O1G.fO%rO`O1G.fO%wO`O1G.fO%|O`O1G.fO&RO`O7+$QO&WOPO7+$QO&`OPO7+$QO&eOPO7+$QO&jOPO7+$QOOQO<<Gl<<GlO&oO`O<<GlO&tOPO<<GlO&yO`O<<GlO'OOPOAN=WO'TO`OAN=WO'YOPOAN=WOOQOG22rG22rO'_OPOG22rO'dO`OG22rO'iO`OLD(^O'nOPOLD(^O'sOPO!$'KxO'xO`O!$'KxO'}O`O!)9AdO(SOPO!)9AdO(XOPO!.K7OOOQO!.K7O!.K7OOOQO!4/,j!4/,j",
  stateData: "(^~OZOSPOS~O[PO]QO_RO`ROaSOcROdTOfROgUOiROjVOlROnROoPOpPOqWOsPOtPOuROwXOyYO!PZO!S[O~OT`O~OTaO~OTbO~OTcO~OTdO~OTeO~OTfO~OTgO~OThO~OTiO~OTjO~OVkO~O^mO~OUnO~ObmO~OenO~OhmO~OkmOmmOvmO~OrmO~OxmO~OzoO}pO!OqO~O!QrO~O!TpO~OTsO~OTtO~OTuO~OTvO~OTwO~OUxO~O{xO|yO~O{xO~O{zO~O|{O~OT|O~O!P}O~OT!OO~O{!PO~OT!QO~O!R!RO~O!Q!SO~OT!TO~OT!UO~O|!VO~O!R!WO~OT!XO~OT!YO~O{!ZO~O{![O~O",
  goto: "hXPPPY^PPPbT^O_T]O_Q_ORl_",
  nodeNames: "\u26A0 Comment Program Sentence WaterproofTactic TacticInput dotSpace CoqSentence",
  maxTerm: 51,
  skippedNodes: [0, 1],
  repeatNodeCount: 1,
  tokenData: "%*p~RnOX#PXY#nYZ#nZ]#P]^#n^p#Ppq$Sqx#Pxy/wyz2{z!O#P!P!c#P!c!d!+{!d!e!2T!e!f!8_!f!g!B^!g!h!Ex!h!j#P!j!k#(h!k!l#*m!l!q#P!q!r#=a!r!u#P!u!v#Dm!v!w#HX!w!y#P!y!z#Jq!z;'S#P;'S;=`#h<%lO#PS#STO!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#PS#hOVSS#kP;=`<%l#PU#sTZUO!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#Pn$X]ZUOy#Pyz%Qz!O#P!O!P#c!P![#P![!]%k!]#T#P#T#U'o#U#]#P#]#^.a#^;'S#P;'S;=`#h<%lO#P[%TTO!O#P!O!P%d!P;'S#P;'S;=`#h<%lO#P[%kOeWVSl%nXOp#Ppq&Zq!O#P!O!P#c!P!_#P!_!`&o!`;'S#P;'S;=`#h<%lO#P[&`T^WO!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#Pl&tVbWOp#Ppq'Zq!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#Pd'`Tx`O!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#P['rVO!O#P!O!P#c!P#V#P#V#W(X#W;'S#P;'S;=`#h<%lO#P[([VO!O#P!O!P#c!P#V#P#V#W(q#W;'S#P;'S;=`#h<%lO#P[(tVO!O#P!O!P#c!P#c#P#c#d)Z#d;'S#P;'S;=`#h<%lO#P[)^VO!O#P!O!P#c!P#f#P#f#g)s#g;'S#P;'S;=`#h<%lO#P[)vVO!O#P!O!P#c!P#W#P#W#X*]#X;'S#P;'S;=`#h<%lO#P[*`VO!O#P!O!P#c!P#]#P#]#^*u#^;'S#P;'S;=`#h<%lO#P[*xVO!O#P!O!P#c!P#b#P#b#c+_#c;'S#P;'S;=`#h<%lO#P[+bVO!O#P!O!P#c!P#Z#P#Z#[+w#[;'S#P;'S;=`#h<%lO#P[+zVOp#Ppq,aq!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#P[,dVO!O#P!O!P#c!P#h#P#h#i,y#i;'S#P;'S;=`#h<%lO#P[,|VO!O#P!O!P#c!P#c#P#c#d-c#d;'S#P;'S;=`#h<%lO#P[-fVOp#Ppq-{q!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#P[.QThWO!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#P[.dVO!O#P!O!P#c!P#b#P#b#c.y#c;'S#P;'S;=`#h<%lO#P[.|VOp#Ppq/cq!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#P[/hTrWO!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#P~/zXOv#Pvw0gwz#Pz{1e{!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#PU0jVOp#Ppq1Pq!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#PU1UTdQO!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#P~1hVOz#Pz{1}{!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#P~2QVOy#Pyz2gz!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#P~2lTP~O!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#P^3OVOp#Ppq3eq!O#P!O!P!+t!P;'S#P;'S;=`#h<%lO#P^3h`Ox#Pxy4jy!O#P!O!P#c!P#T#P#T#U5O#U#V7h#V#]#P#]#^:j#^#c#P#c#dNd#d#k#P#k#l!!d#l;'S#P;'S;=`#h<%lO#PU4oT|QO!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#PU5RVO!O#P!O!P#c!P#b#P#b#c5h#c;'S#P;'S;=`#h<%lO#PU5kVO!O#P!O!P#c!P#W#P#W#X6Q#X;'S#P;'S;=`#h<%lO#PU6TVOp#Ppq6jq!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#PU6mVOx#Pxy7Sy!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#PU7XT!RQO!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#PU7kVO!O#P!O!P#c!P#c#P#c#d8Q#d;'S#P;'S;=`#h<%lO#PU8TVO!O#P!O!P#c!P#h#P#h#i8j#i;'S#P;'S;=`#h<%lO#PU8mVO!O#P!O!P#c!P#[#P#[#]9S#];'S#P;'S;=`#h<%lO#PU9VVOp#Ppq9lq!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#PU9oVOx#Pxy:Uy!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#PU:ZT!QQO!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#P^:mVO!O#P!O!P#c!P#h#P#h#i;S#i;'S#P;'S;=`#h<%lO#P^;VVOp#Ppq;lq!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#P^;oXO!O#P!O!P#c!P#[#P#[#]<[#]#g#P#g#hBf#h;'S#P;'S;=`#h<%lO#P^<_VO!O#P!O!P#c!P#c#P#c#d<t#d;'S#P;'S;=`#h<%lO#P^<wVO!O#P!O!P#c!P#`#P#`#a=^#a;'S#P;'S;=`#h<%lO#P^=aVO!O#P!O!P#c!P#W#P#W#X=v#X;'S#P;'S;=`#h<%lO#P^=yVO!O#P!O!P#c!P#g#P#g#h>`#h;'S#P;'S;=`#h<%lO#P^>cVOp#Ppq>xq!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#P^>{VO!O#P!O!P#c!P#h#P#h#i?b#i;'S#P;'S;=`#h<%lO#P^?eVO!O#P!O!P#c!P#[#P#[#]?z#];'S#P;'S;=`#h<%lO#P^?}VO!O#P!O!P#c!P#T#P#T#U@d#U;'S#P;'S;=`#h<%lO#P^@gVO!O#P!O!P#c!P#h#P#h#i@|#i;'S#P;'S;=`#h<%lO#P^APVOp#PpqAfq!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#P^AkVmQOx#PxyBQy!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#P[BVTzWO!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#P^BiVO!O#P!O!P#c!P#i#P#i#jCO#j;'S#P;'S;=`#h<%lO#P^CRVO!O#P!O!P#c!P#Y#P#Y#ZCh#Z;'S#P;'S;=`#h<%lO#P^CkVO!O#P!O!P#c!P#Y#P#Y#ZDQ#Z;'S#P;'S;=`#h<%lO#P^DTVO!O#P!O!P#c!P#]#P#]#^Dj#^;'S#P;'S;=`#h<%lO#P^DmVO!O#P!O!P#c!P#V#P#V#WES#W;'S#P;'S;=`#h<%lO#P^EVVO!O#P!O!P#c!P#X#P#X#YEl#Y;'S#P;'S;=`#h<%lO#P^EoVO!O#P!O!P#c!P#g#P#g#hFU#h;'S#P;'S;=`#h<%lO#P^FXVOp#PpqFnq!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#P^FqVO!O#P!O!P#c!P#h#P#h#iGW#i;'S#P;'S;=`#h<%lO#P^GZVO!O#P!O!P#c!P#c#P#c#dGp#d;'S#P;'S;=`#h<%lO#P^GsVOp#PpqHYq!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#P^H]VO!O#P!O!P#c!P#g#P#g#hHr#h;'S#P;'S;=`#h<%lO#P^HuVO!O#P!O!P#c!P#[#P#[#]I[#];'S#P;'S;=`#h<%lO#P^I_VO!O#P!O!P#c!P#c#P#c#dIt#d;'S#P;'S;=`#h<%lO#P^IwVO!O#P!O!P#c!P#k#P#k#lJ^#l;'S#P;'S;=`#h<%lO#P^JaVOp#PpqJvq!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#P^JyVO!O#P!O!P#c!P#h#P#h#iK`#i;'S#P;'S;=`#h<%lO#P^KcVO!O#P!O!P#c!P#[#P#[#]Kx#];'S#P;'S;=`#h<%lO#P^K{VO!O#P!O!P#c!P#T#P#T#ULb#U;'S#P;'S;=`#h<%lO#P^LeVO!O#P!O!P#c!P#h#P#h#iLz#i;'S#P;'S;=`#h<%lO#P^L}VOp#PpqMdq!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#P^MiVkQOx#PxyNOy!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#P[NTT!OWO!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#PUNgVO!O#P!O!P#c!P#f#P#f#gN|#g;'S#P;'S;=`#h<%lO#PU! PVOp#Ppq! fq!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#PU! iVOx#Pxy!!Oy!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#PU!!TT!TQO!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#P^!!gVO!O#P!O!P#c!P#X#P#X#Y!!|#Y;'S#P;'S;=`#h<%lO#P^!#PVOp#Ppq!#fq!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#P^!#iVO!O#P!O!P#c!P#V#P#V#W!$O#W;'S#P;'S;=`#h<%lO#P^!$RVO!O#P!O!P#c!P#c#P#c#d!$h#d;'S#P;'S;=`#h<%lO#P^!$kVO!O#P!O!P#c!P#b#P#b#c!%Q#c;'S#P;'S;=`#h<%lO#P^!%TVO!O#P!O!P#c!P#V#P#V#W!%j#W;'S#P;'S;=`#h<%lO#P^!%mVO!O#P!O!P#c!P#`#P#`#a!&S#a;'S#P;'S;=`#h<%lO#P^!&VVO!O#P!O!P#c!P#i#P#i#j!&l#j;'S#P;'S;=`#h<%lO#P^!&oVO!O#P!O!P#c!P#W#P#W#X!'U#X;'S#P;'S;=`#h<%lO#P^!'XVO!O#P!O!P#c!P#X#P#X#Y!'n#Y;'S#P;'S;=`#h<%lO#P^!'qVOp#Ppq!(Wq!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#P^!(ZVO!O#P!O!P#c!P#h#P#h#i!(p#i;'S#P;'S;=`#h<%lO#P^!(sVO!O#P!O!P#c!P#[#P#[#]!)Y#];'S#P;'S;=`#h<%lO#P^!)]VO!O#P!O!P#c!P#T#P#T#U!)r#U;'S#P;'S;=`#h<%lO#P^!)uVO!O#P!O!P#c!P#h#P#h#i!*[#i;'S#P;'S;=`#h<%lO#P^!*_VOp#Ppq!*tq!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#P^!*yVvQOx#Pxy!+`y!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#P[!+eT}WO!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#PU!+{O{QVSU!,OVO!O#P!O!P#c!P#g#P#g#h!,e#h;'S#P;'S;=`#h<%lO#PU!,hVO!O#P!O!P#c!P#g#P#g#h!,}#h;'S#P;'S;=`#h<%lO#PU!-QVO!O#P!O!P#c!P#i#P#i#j!-g#j;'S#P;'S;=`#h<%lO#PU!-jVO!O#P!O!P#c!P#a#P#a#b!.P#b;'S#P;'S;=`#h<%lO#PU!.SVO!O#P!O!P#c!P#X#P#X#Y!.i#Y;'S#P;'S;=`#h<%lO#PU!.lVOp#Ppq!/Rq!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#PU!/UVO!O#P!O!P#c!P#h#P#h#i!/k#i;'S#P;'S;=`#h<%lO#PU!/nVO!O#P!O!P#c!P#[#P#[#]!0T#];'S#P;'S;=`#h<%lO#PU!0WVO!O#P!O!P#c!P#T#P#T#U!0m#U;'S#P;'S;=`#h<%lO#PU!0pVO!O#P!O!P#c!P#h#P#h#i!1V#i;'S#P;'S;=`#h<%lO#PU!1YVOp#Ppq!1oq!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#PU!1tTcQO!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#PU!2WXO!O#P!O!P#c!P#X#P#X#Y!2s#Y#m#P#m#n!6w#n;'S#P;'S;=`#h<%lO#PU!2vVO!O#P!O!P#c!P#V#P#V#W!3]#W;'S#P;'S;=`#h<%lO#PU!3`VO!O#P!O!P#c!P#T#P#T#U!3u#U;'S#P;'S;=`#h<%lO#PU!3xVO!O#P!O!P#c!P#i#P#i#j!4_#j;'S#P;'S;=`#h<%lO#PU!4bVO!O#P!O!P#c!P#g#P#g#h!4w#h;'S#P;'S;=`#h<%lO#PU!4zVO!O#P!O!P#c!P#X#P#X#Y!5a#Y;'S#P;'S;=`#h<%lO#PU!5dVOp#Ppq!5yq!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#PU!5|VOx#Pxy!6cy!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#PU!6hT!PQO!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#PU!6zVOp#Ppq!7aq!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#PU!7dVOx#Pxy!7yy!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#PU!8OTjQO!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#PU!8bXO!O#P!O!P#c!P#[#P#[#]!8}#]#c#P#c#d!<P#d;'S#P;'S;=`#h<%lO#PU!9QVO!O#P!O!P#c!P#c#P#c#d!9g#d;'S#P;'S;=`#h<%lO#PU!9jVO!O#P!O!P#c!P#c#P#c#d!:P#d;'S#P;'S;=`#h<%lO#PU!:SVO!O#P!O!P#c!P#g#P#g#h!:i#h;'S#P;'S;=`#h<%lO#PU!:lVO!O#P!O!P#c!P#X#P#X#Y!;R#Y;'S#P;'S;=`#h<%lO#PU!;UVOp#Ppq!;kq!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#PU!;pTaQO!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#PU!<SVO!O#P!O!P#c!P#b#P#b#c!<i#c;'S#P;'S;=`#h<%lO#PU!<lVO!O#P!O!P#c!P#h#P#h#i!=R#i;'S#P;'S;=`#h<%lO#PU!=UVO!O#P!O!P#c!P#f#P#f#g!=k#g;'S#P;'S;=`#h<%lO#PU!=nVO!O#P!O!P#c!P#T#P#T#U!>T#U;'S#P;'S;=`#h<%lO#PU!>WVO!O#P!O!P#c!P#W#P#W#X!>m#X;'S#P;'S;=`#h<%lO#PU!>pVO!O#P!O!P#c!P#]#P#]#^!?V#^;'S#P;'S;=`#h<%lO#PU!?YVO!O#P!O!P#c!P#V#P#V#W!?o#W;'S#P;'S;=`#h<%lO#PU!?rVO!O#P!O!P#c!P#h#P#h#i!@X#i;'S#P;'S;=`#h<%lO#PU!@[VO!O#P!O!P#c!P#]#P#]#^!@q#^;'S#P;'S;=`#h<%lO#PU!@tVO!O#P!O!P#c!P#c#P#c#d!AZ#d;'S#P;'S;=`#h<%lO#PU!A^VO!O#P!O!P#c!P#b#P#b#c!As#c;'S#P;'S;=`#h<%lO#PU!AvTO!O#P!O!P!BV!P;'S#P;'S;=`#h<%lO#PU!B^OpQVSU!BaVO!O#P!O!P#c!P#X#P#X#Y!Bv#Y;'S#P;'S;=`#h<%lO#PU!ByVO!O#P!O!P#c!P#Y#P#Y#Z!C`#Z;'S#P;'S;=`#h<%lO#PU!CcVO!O#P!O!P#c!P#]#P#]#^!Cx#^;'S#P;'S;=`#h<%lO#PU!C{VO!O#P!O!P#c!P#b#P#b#c!Db#c;'S#P;'S;=`#h<%lO#PU!DeVO!O#P!O!P#c!P#X#P#X#Y!Dz#Y;'S#P;'S;=`#h<%lO#PU!D}VOp#Ppq!Edq!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#PU!EiTwQO!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#PU!E{XO!O#P!O!P#c!P#]#P#]#^!Fh#^#l#P#l#m!JS#m;'S#P;'S;=`#h<%lO#PU!FkVO!O#P!O!P#c!P#h#P#h#i!GQ#i;'S#P;'S;=`#h<%lO#PU!GTVO!O#P!O!P#c!P#[#P#[#]!Gj#];'S#P;'S;=`#h<%lO#PU!GmVO!O#P!O!P#c!P#X#P#X#Y!HS#Y;'S#P;'S;=`#h<%lO#PU!HVVO!O#P!O!P#c!P#f#P#f#g!Hl#g;'S#P;'S;=`#h<%lO#PU!HoVOp#Ppq!IUq!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#PU!IXVOx#Pxy!Iny!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#PU!IsT!SQO!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#PU!JVVO!O#P!O!P#c!P#d#P#d#e!Jl#e;'S#P;'S;=`#h<%lO#PU!JoVO!O#P!O!P#c!P#T#P#T#U!KU#U;'S#P;'S;=`#h<%lO#PU!KXVO!O#P!O!P#c!P#b#P#b#c!Kn#c;'S#P;'S;=`#h<%lO#PU!KqVO!O#P!O!P#c!P#W#P#W#X!LW#X;'S#P;'S;=`#h<%lO#PU!LZVOp#Ppq!Lpq!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#PU!LsVO!O#P!O!P#c!P#h#P#h#i!MY#i;'S#P;'S;=`#h<%lO#PU!M]VO!O#P!O!P#c!P#[#P#[#]!Mr#];'S#P;'S;=`#h<%lO#PU!MuVO!O#P!O!P#c!P#X#P#X#Y!N[#Y;'S#P;'S;=`#h<%lO#PU!N_VOp#Ppq!Ntq!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#PU!NwVO!O#P!O!P#c!P#W#P#W#X# ^#X;'S#P;'S;=`#h<%lO#PU# aVO!O#P!O!P#c!P#X#P#X#Y# v#Y;'S#P;'S;=`#h<%lO#PU# yVO!O#P!O!P#c!P#Y#P#Y#Z#!`#Z;'S#P;'S;=`#h<%lO#PU#!cVO!O#P!O!P#c!P#]#P#]#^#!x#^;'S#P;'S;=`#h<%lO#PU#!{VO!O#P!O!P#c!P#b#P#b#c##b#c;'S#P;'S;=`#h<%lO#PU##eVO!O#P!O!P#c!P#]#P#]#^##z#^;'S#P;'S;=`#h<%lO#PU##}VO!O#P!O!P#c!P#h#P#h#i#$d#i;'S#P;'S;=`#h<%lO#PU#$gVO!O#P!O!P#c!P#]#P#]#^#$|#^;'S#P;'S;=`#h<%lO#PU#%PVO!O#P!O!P#c!P#c#P#c#d#%f#d;'S#P;'S;=`#h<%lO#PU#%iVO!O#P!O!P#c!P#b#P#b#c#&O#c;'S#P;'S;=`#h<%lO#PU#&RVOp#Ppq#&hq!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#PU#&kVO!O#P!O!P#c!P#c#P#c#d#'Q#d;'S#P;'S;=`#h<%lO#PU#'TVO!O#P!O!P#c!P#Y#P#Y#Z#'j#Z;'S#P;'S;=`#h<%lO#PU#'mVOp#Ppq#(Sq!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#PU#(XTqQO!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#PU#(kVO!O#P!O!P#c!P#X#P#X#Y#)Q#Y;'S#P;'S;=`#h<%lO#PU#)TVO!O#P!O!P#c!P#`#P#`#a#)j#a;'S#P;'S;=`#h<%lO#PU#)mVO!O#P!O!P#c!P#d#P#d#e#*S#e;'S#P;'S;=`#h<%lO#PU#*VTO!O#P!O!P#*f!P;'S#P;'S;=`#h<%lO#PU#*mO[QVSU#*pVO!O#P!O!P#c!P#h#P#h#i#+V#i;'S#P;'S;=`#h<%lO#PU#+YVOp#Ppq#+oq!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#PU#+rXO!O#P!O!P#c!P#[#P#[#]#,_#]#g#P#g#h#1}#h;'S#P;'S;=`#h<%lO#PU#,bVO!O#P!O!P#c!P#c#P#c#d#,w#d;'S#P;'S;=`#h<%lO#PU#,zVO!O#P!O!P#c!P#`#P#`#a#-a#a;'S#P;'S;=`#h<%lO#PU#-dVO!O#P!O!P#c!P#W#P#W#X#-y#X;'S#P;'S;=`#h<%lO#PU#-|VO!O#P!O!P#c!P#g#P#g#h#.c#h;'S#P;'S;=`#h<%lO#PU#.fVOp#Ppq#.{q!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#PU#/OVO!O#P!O!P#c!P#h#P#h#i#/e#i;'S#P;'S;=`#h<%lO#PU#/hVO!O#P!O!P#c!P#[#P#[#]#/}#];'S#P;'S;=`#h<%lO#PU#0QVO!O#P!O!P#c!P#T#P#T#U#0g#U;'S#P;'S;=`#h<%lO#PU#0jVO!O#P!O!P#c!P#h#P#h#i#1P#i;'S#P;'S;=`#h<%lO#PU#1SVOp#Ppq#1iq!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#PU#1nTlQO!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#PU#2QVO!O#P!O!P#c!P#i#P#i#j#2g#j;'S#P;'S;=`#h<%lO#PU#2jVO!O#P!O!P#c!P#Y#P#Y#Z#3P#Z;'S#P;'S;=`#h<%lO#PU#3SVO!O#P!O!P#c!P#Y#P#Y#Z#3i#Z;'S#P;'S;=`#h<%lO#PU#3lVO!O#P!O!P#c!P#]#P#]#^#4R#^;'S#P;'S;=`#h<%lO#PU#4UVO!O#P!O!P#c!P#V#P#V#W#4k#W;'S#P;'S;=`#h<%lO#PU#4nVO!O#P!O!P#c!P#X#P#X#Y#5T#Y;'S#P;'S;=`#h<%lO#PU#5WVO!O#P!O!P#c!P#g#P#g#h#5m#h;'S#P;'S;=`#h<%lO#PU#5pVOp#Ppq#6Vq!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#PU#6YVO!O#P!O!P#c!P#h#P#h#i#6o#i;'S#P;'S;=`#h<%lO#PU#6rVO!O#P!O!P#c!P#c#P#c#d#7X#d;'S#P;'S;=`#h<%lO#PU#7[VOp#Ppq#7qq!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#PU#7tVO!O#P!O!P#c!P#g#P#g#h#8Z#h;'S#P;'S;=`#h<%lO#PU#8^VO!O#P!O!P#c!P#[#P#[#]#8s#];'S#P;'S;=`#h<%lO#PU#8vVO!O#P!O!P#c!P#c#P#c#d#9]#d;'S#P;'S;=`#h<%lO#PU#9`VO!O#P!O!P#c!P#k#P#k#l#9u#l;'S#P;'S;=`#h<%lO#PU#9xVOp#Ppq#:_q!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#PU#:bVO!O#P!O!P#c!P#h#P#h#i#:w#i;'S#P;'S;=`#h<%lO#PU#:zVO!O#P!O!P#c!P#[#P#[#]#;a#];'S#P;'S;=`#h<%lO#PU#;dVO!O#P!O!P#c!P#T#P#T#U#;y#U;'S#P;'S;=`#h<%lO#PU#;|VO!O#P!O!P#c!P#h#P#h#i#<c#i;'S#P;'S;=`#h<%lO#PU#<fVOp#Ppq#<{q!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#PU#=QTiQO!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#PU#=dVO!O#P!O!P#c!P#U#P#U#V#=y#V;'S#P;'S;=`#h<%lO#PU#=|VO!O#P!O!P#c!P#h#P#h#i#>c#i;'S#P;'S;=`#h<%lO#PU#>fVO!O#P!O!P#c!P#T#P#T#U#>{#U;'S#P;'S;=`#h<%lO#PU#?OVO!O#P!O!P#c!P#]#P#]#^#?e#^;'S#P;'S;=`#h<%lO#PU#?hVO!O#P!O!P#c!P#b#P#b#c#?}#c;'S#P;'S;=`#h<%lO#PU#@QVOp#Ppq#@gq!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#PU#@lVgQO!O#P!O!P#c!P#g#P#g#h#AR#h;'S#P;'S;=`#h<%lO#PU#AUVO!O#P!O!P#c!P#i#P#i#j#Ak#j;'S#P;'S;=`#h<%lO#PU#AnVO!O#P!O!P#c!P#V#P#V#W#BT#W;'S#P;'S;=`#h<%lO#PU#BWVO!O#P!O!P#c!P#[#P#[#]#Bm#];'S#P;'S;=`#h<%lO#PU#BpVOp#Ppq#CVq!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#PU#CYVO!O#P!O!P#c!P#T#P#T#U#Co#U;'S#P;'S;=`#h<%lO#PU#CrVOp#Ppq#DXq!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#PU#D^TfQO!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#PU#DpVO!O#P!O!P#c!P#]#P#]#^#EV#^;'S#P;'S;=`#h<%lO#PU#EYVO!O#P!O!P#c!P#b#P#b#c#Eo#c;'S#P;'S;=`#h<%lO#PU#ErVO!O#P!O!P#c!P#V#P#V#W#FX#W;'S#P;'S;=`#h<%lO#PU#F[VO!O#P!O!P#c!P#X#P#X#Y#Fq#Y;'S#P;'S;=`#h<%lO#PU#FtVOp#Ppq#GZq!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#PU#G^VOx#Pxy#Gsy!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#PU#GxTyQO!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#PU#H[VO!O#P!O!P#c!P#T#P#T#U#Hq#U;'S#P;'S;=`#h<%lO#PU#HtVO!O#P!O!P#c!P#_#P#_#`#IZ#`;'S#P;'S;=`#h<%lO#PU#I^VO!O#P!O!P#c!P#X#P#X#Y#Is#Y;'S#P;'S;=`#h<%lO#PU#IvVOp#Ppq#J]q!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#PU#JbT]QO!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#PU#JtVO!O#P!O!P#c!P#X#P#X#Y#KZ#Y;'S#P;'S;=`#h<%lO#PU#K^VOp#Ppq#Ksq!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#PU#Kv_O!O#P!O!P#c!P#T#P#T#U#Lu#U#V#P#V#W$*^#W#b#P#b#c$6t#c#g#P#g#h$@S#h#i#P#i#j% z#j;'S#P;'S;=`#h<%lO#PU#LxVO!O#P!O!P#c!P#f#P#f#g#M_#g;'S#P;'S;=`#h<%lO#PU#MbVO!O#P!O!P#c!P#Z#P#Z#[#Mw#[;'S#P;'S;=`#h<%lO#PU#MzVO!O#P!O!P#c!P#i#P#i#j#Na#j;'S#P;'S;=`#h<%lO#PU#NdVO!O#P!O!P#c!P#X#P#X#Y#Ny#Y;'S#P;'S;=`#h<%lO#PU#N|VOp#Ppq$ cq!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#PU$ fVO!O#P!O!P#c!P#U#P#U#V$ {#V;'S#P;'S;=`#h<%lO#PU$!OVO!O#P!O!P#c!P#m#P#m#n$!e#n;'S#P;'S;=`#h<%lO#PU$!hVOp#Ppq$!}q!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#PU$#QVO!O#P!O!P#c!P#V#P#V#W$#g#W;'S#P;'S;=`#h<%lO#PU$#jVO!O#P!O!P#c!P#c#P#c#d$$P#d;'S#P;'S;=`#h<%lO#PU$$SVO!O#P!O!P#c!P#b#P#b#c$$i#c;'S#P;'S;=`#h<%lO#PU$$lVO!O#P!O!P#c!P#h#P#h#i$%R#i;'S#P;'S;=`#h<%lO#PU$%UVO!O#P!O!P#c!P#f#P#f#g$%k#g;'S#P;'S;=`#h<%lO#PU$%nVO!O#P!O!P#c!P#T#P#T#U$&T#U;'S#P;'S;=`#h<%lO#PU$&WVO!O#P!O!P#c!P#W#P#W#X$&m#X;'S#P;'S;=`#h<%lO#PU$&pVO!O#P!O!P#c!P#]#P#]#^$'V#^;'S#P;'S;=`#h<%lO#PU$'YVO!O#P!O!P#c!P#V#P#V#W$'o#W;'S#P;'S;=`#h<%lO#PU$'rVO!O#P!O!P#c!P#h#P#h#i$(X#i;'S#P;'S;=`#h<%lO#PU$([VO!O#P!O!P#c!P#]#P#]#^$(q#^;'S#P;'S;=`#h<%lO#PU$(tVO!O#P!O!P#c!P#c#P#c#d$)Z#d;'S#P;'S;=`#h<%lO#PU$)^VO!O#P!O!P#c!P#b#P#b#c$)s#c;'S#P;'S;=`#h<%lO#PU$)vTO!O#P!O!P$*V!P;'S#P;'S;=`#h<%lO#PU$*^OoQVSU$*aXO!O#P!O!P#c!P#`#P#`#a$*|#a#c#P#c#d$0S#d;'S#P;'S;=`#h<%lO#PU$+PVO!O#P!O!P#c!P#T#P#T#U$+f#U;'S#P;'S;=`#h<%lO#PU$+iVO!O#P!O!P#c!P#]#P#]#^$,O#^;'S#P;'S;=`#h<%lO#PU$,RVO!O#P!O!P#c!P#a#P#a#b$,h#b;'S#P;'S;=`#h<%lO#PU$,kVOp#Ppq$-Qq!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#PU$-TVO!O#P!O!P#c!P#h#P#h#i$-j#i;'S#P;'S;=`#h<%lO#PU$-mVO!O#P!O!P#c!P#[#P#[#]$.S#];'S#P;'S;=`#h<%lO#PU$.VVO!O#P!O!P#c!P#T#P#T#U$.l#U;'S#P;'S;=`#h<%lO#PU$.oVO!O#P!O!P#c!P#h#P#h#i$/U#i;'S#P;'S;=`#h<%lO#PU$/XVOp#Ppq$/nq!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#PU$/sTnQO!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#PU$0VVO!O#P!O!P#c!P#b#P#b#c$0l#c;'S#P;'S;=`#h<%lO#PU$0oVO!O#P!O!P#c!P#V#P#V#W$1U#W;'S#P;'S;=`#h<%lO#PU$1XVO!O#P!O!P#c!P#`#P#`#a$1n#a;'S#P;'S;=`#h<%lO#PU$1qVO!O#P!O!P#c!P#i#P#i#j$2W#j;'S#P;'S;=`#h<%lO#PU$2ZVO!O#P!O!P#c!P#W#P#W#X$2p#X;'S#P;'S;=`#h<%lO#PU$2sVO!O#P!O!P#c!P#X#P#X#Y$3Y#Y;'S#P;'S;=`#h<%lO#PU$3]VOp#Ppq$3rq!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#PU$3uVO!O#P!O!P#c!P#h#P#h#i$4[#i;'S#P;'S;=`#h<%lO#PU$4_VO!O#P!O!P#c!P#[#P#[#]$4t#];'S#P;'S;=`#h<%lO#PU$4wVO!O#P!O!P#c!P#T#P#T#U$5^#U;'S#P;'S;=`#h<%lO#PU$5aVO!O#P!O!P#c!P#h#P#h#i$5v#i;'S#P;'S;=`#h<%lO#PU$5yVOp#Ppq$6`q!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#PU$6eT`QO!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#PU$6wVO!O#P!O!P#c!P#X#P#X#Y$7^#Y;'S#P;'S;=`#h<%lO#PU$7aVO!O#P!O!P#c!P#X#P#X#Y$7v#Y;'S#P;'S;=`#h<%lO#PU$7yVO!O#P!O!P#c!P#W#P#W#X$8`#X;'S#P;'S;=`#h<%lO#PU$8cVOp#Ppq$8xq!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#PU$8{VO!O#P!O!P#c!P#h#P#h#i$9b#i;'S#P;'S;=`#h<%lO#PU$9eVO!O#P!O!P#c!P#c#P#c#d$9z#d;'S#P;'S;=`#h<%lO#PU$9}VOp#Ppq$:dq!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#PU$:gVO!O#P!O!P#c!P#g#P#g#h$:|#h;'S#P;'S;=`#h<%lO#PU$;PVO!O#P!O!P#c!P#[#P#[#]$;f#];'S#P;'S;=`#h<%lO#PU$;iVO!O#P!O!P#c!P#c#P#c#d$<O#d;'S#P;'S;=`#h<%lO#PU$<RVO!O#P!O!P#c!P#k#P#k#l$<h#l;'S#P;'S;=`#h<%lO#PU$<kVOp#Ppq$=Qq!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#PU$=TVO!O#P!O!P#c!P#h#P#h#i$=j#i;'S#P;'S;=`#h<%lO#PU$=mVO!O#P!O!P#c!P#[#P#[#]$>S#];'S#P;'S;=`#h<%lO#PU$>VVO!O#P!O!P#c!P#T#P#T#U$>l#U;'S#P;'S;=`#h<%lO#PU$>oVO!O#P!O!P#c!P#h#P#h#i$?U#i;'S#P;'S;=`#h<%lO#PU$?XVOp#Ppq$?nq!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#PU$?sT_QO!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#PU$@VVO!O#P!O!P#c!P#[#P#[#]$@l#];'S#P;'S;=`#h<%lO#PU$@oVO!O#P!O!P#c!P#c#P#c#d$AU#d;'S#P;'S;=`#h<%lO#PU$AXVO!O#P!O!P#c!P#k#P#k#l$An#l;'S#P;'S;=`#h<%lO#PU$AqVOp#Ppq$BWq!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#PU$BZVO!O#P!O!P#c!P#U#P#U#V$Bp#V;'S#P;'S;=`#h<%lO#PU$BsVO!O#P!O!P#c!P#c#P#c#d$CY#d;'S#P;'S;=`#h<%lO#PU$C]VO!O#P!O!P#c!P#h#P#h#i$Cr#i;'S#P;'S;=`#h<%lO#PU$CuVO!O#P!O!P#c!P#[#P#[#]$D[#];'S#P;'S;=`#h<%lO#PU$D_VOp#Ppq$Dtq!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#PU$DwXO!O#P!O!P#c!P#W#P#W#X$Ed#X#g#P#g#h$Jo#h;'S#P;'S;=`#h<%lO#PU$EgVO!O#P!O!P#c!P#]#P#]#^$E|#^;'S#P;'S;=`#h<%lO#PU$FPVO!O#P!O!P#c!P#f#P#f#g$Ff#g;'S#P;'S;=`#h<%lO#PU$FiVO!O#P!O!P#c!P#X#P#X#Y$GO#Y;'S#P;'S;=`#h<%lO#PU$GRVO!O#P!O!P#c!P#V#P#V#W$Gh#W;'S#P;'S;=`#h<%lO#PU$GkVO!O#P!O!P#c!P#h#P#h#i$HQ#i;'S#P;'S;=`#h<%lO#PU$HTVO!O#P!O!P#c!P#]#P#]#^$Hj#^;'S#P;'S;=`#h<%lO#PU$HmVO!O#P!O!P#c!P#c#P#c#d$IS#d;'S#P;'S;=`#h<%lO#PU$IVVO!O#P!O!P#c!P#b#P#b#c$Il#c;'S#P;'S;=`#h<%lO#PU$IoVO!O#P!O!P#c!P#g#P#g#h$JU#h;'S#P;'S;=`#h<%lO#PU$JXTO!O#P!O!P$Jh!P;'S#P;'S;=`#h<%lO#PU$JoOtQVSU$JrVO!O#P!O!P#c!P#h#P#h#i$KX#i;'S#P;'S;=`#h<%lO#PU$K[VO!O#P!O!P#c!P#T#P#T#U$Kq#U;'S#P;'S;=`#h<%lO#PU$KtVO!O#P!O!P#c!P#h#P#h#i$LZ#i;'S#P;'S;=`#h<%lO#PU$L^VO!O#P!O!P#c!P#X#P#X#Y$Ls#Y;'S#P;'S;=`#h<%lO#PU$LvVO!O#P!O!P#c!P#a#P#a#b$M]#b;'S#P;'S;=`#h<%lO#PU$M`VO!O#P!O!P#c!P#X#P#X#Y$Mu#Y;'S#P;'S;=`#h<%lO#PU$MxVO!O#P!O!P#c!P#b#P#b#c$N_#c;'S#P;'S;=`#h<%lO#PU$NbVO!O#P!O!P#c!P#h#P#h#i$Nw#i;'S#P;'S;=`#h<%lO#PU$NzVO!O#P!O!P#c!P#g#P#g#h% a#h;'S#P;'S;=`#h<%lO#PU% dTO!O#P!O!P% s!P;'S#P;'S;=`#h<%lO#PU% zOsQVSU% }VO!O#P!O!P#c!P#g#P#g#h%!d#h;'S#P;'S;=`#h<%lO#PU%!gVO!O#P!O!P#c!P#X#P#X#Y%!|#Y;'S#P;'S;=`#h<%lO#PU%#PVOp#Ppq%#fq!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#PU%#iVO!O#P!O!P#c!P#]#P#]#^%$O#^;'S#P;'S;=`#h<%lO#PU%$RVO!O#P!O!P#c!P#b#P#b#c%$h#c;'S#P;'S;=`#h<%lO#PU%$kVO!O#P!O!P#c!P#W#P#W#X%%Q#X;'S#P;'S;=`#h<%lO#PU%%TVO!O#P!O!P#c!P#i#P#i#j%%j#j;'S#P;'S;=`#h<%lO#PU%%mVO!O#P!O!P#c!P#V#P#V#W%&S#W;'S#P;'S;=`#h<%lO#PU%&VVO!O#P!O!P#c!P#h#P#h#i%&l#i;'S#P;'S;=`#h<%lO#PU%&oVO!O#P!O!P#c!P#]#P#]#^%'U#^;'S#P;'S;=`#h<%lO#PU%'XVO!O#P!O!P#c!P#c#P#c#d%'n#d;'S#P;'S;=`#h<%lO#PU%'qVO!O#P!O!P#c!P#b#P#b#c%(W#c;'S#P;'S;=`#h<%lO#PU%(ZVOp#Ppq%(pq!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#PU%(sVO!O#P!O!P#c!P#c#P#c#d%)Y#d;'S#P;'S;=`#h<%lO#PU%)]VO!O#P!O!P#c!P#b#P#b#c%)r#c;'S#P;'S;=`#h<%lO#PU%)uVOp#Ppq%*[q!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#PU%*aTuQO!O#P!O!P#c!P;'S#P;'S;=`#h<%lO#P",
  tokenizers: [1, 2, 3, 4, new LocalTokenGroup("k~RP!O!PU~XSXYeYZe]^epqe~jOU~~", 26, 5)],
  topRules: { "Program": [0, 2] },
  tokenPrec: 0
});

// parser-debug-tool.mjs
var import_fs = require("fs");
function printJSON(input) {
  console.log(JSON.stringify(parser.parse(input), null, 2));
}
var fileContents = (0, import_fs.readFileSync)("input.txt", "utf8");
console.log(fileContents);
printJSON(fileContents);
