const std = @import("std");
const assert = std.debug.assert;
const Order = std.math.Order;
pub const bst = @import("binary_search_tree.zig");

const Error = bst.Error;

/// Red Black Tree implementation from Cormen Introduction to Algorithms, third edition, chapter 13.
/// Properties of red black tree:
///   * every node is either black or red
///   * root is black
///   * if node is red than both children are black
///   * for each node, all simple paths from the node to descendant leaves contain the same number of black nodes
///
/// Implementation in book uses sentinel nil node for all leafs. I'm not using
/// that in this implementation in order to reuse node from BinarySearchTreeNode
/// which uses null pointers not sentinel.
///
pub fn RedBlackTree(
    comptime K: type, // key data type
    comptime T: type, // value data type
    comptime Context: type,
    comptime compareFn: *const fn (ctx: Context, a: K, b: K) Order,
) type {
    return struct {
        pub const Node = bst.BinarySearchTreeNode(K, T, true);

        const Self = @This();

        root: ?*Node = null,
        context: Context,
        node_count: usize = 0,

        /// Inserts a new `Node` into the tree, returning the previous one, if any.
        /// If node with the same key if found it is replaced with n and the previous is returned.
        /// So the caller has chance to deinit unused node.
        /// If key don't exists returns null.
        pub fn fetchPut(self: *Self, n: *Node) ?*Node {
            if (self.fetchPut_(n)) |x| {
                x.replace(n);
                return x;
            }
            return null;
        }

        /// Puts new node into tree if that key not exists.
        /// If the key is already in the tree returns error.
        pub fn putNoClobber(self: *Self, n: *Node) Error!void {
            if (self.fetchPut_(n)) |x| {
                assert(x.key == n.key);
                return Error.KeyExists;
            }
        }

        //  Inserts node n into tree or returns existing one with the same key.
        fn fetchPut_(self: *Self, n: *Node) ?*Node {
            assert(n.left == null and n.right == null and n.prev == null);
            var x: *Node = self.root orelse {
                self.node_count = 1;
                n.color = .black;
                self.root = n;
                return null;
            };
            n.color = .red;
            while (true) {
                x = switch (compareFn(self.context, n.key, x.key)) {
                    .lt => x.left orelse {
                        self.node_count += 1;
                        n.prev = x;
                        x.left = n;
                        self.putBalance(n);
                        return null;
                    },
                    .gt => x.right orelse {
                        self.node_count += 1;
                        n.prev = x;
                        x.right = n;
                        self.putBalance(n);
                        return null;
                    },
                    .eq => {
                        return x;
                    },
                };
            }
        }

        /// Balance tree after putting node n.
        fn putBalance(self: *Self, n: *Node) void {
            var z = n;
            while (true) {
                const p = z.prev orelse break; // z is root
                if (p.color == .black) break;
                const pp = p.prev orelse break; // z is depth 1
                if (p == pp.left) {
                    if (pp.right) |y| {
                        if (y.color == .red) {
                            p.color = .black;
                            y.color = .black;
                            pp.color = .red;
                            z = pp;
                            continue;
                        }
                    }
                    if (z == p.right) {
                        z = p;
                        self.leftRotate(z);
                    }
                    if (z.prev) |zp| {
                        zp.color = .black;
                        if (zp.prev) |zpp| {
                            zpp.color = .red;
                            self.rightRotate(zpp);
                        }
                    }
                } else {
                    if (pp.left) |y| {
                        if (y.color == .red) {
                            p.color = .black;
                            y.color = .black;
                            pp.color = .red;
                            z = pp;
                            continue;
                        }
                    }
                    if (z == p.left) {
                        z = p;
                        self.rightRotate(z);
                    }
                    if (z.prev) |zp| {
                        zp.color = .black;
                        if (zp.prev) |zpp| {
                            zpp.color = .red;
                            self.leftRotate(zpp);
                        }
                    }
                }
            }
            if (self.root) |root| root.color = .black;
        }

        /// Left rotate x node with its parent (y node)
        ///
        ///
        ///     |                                      |
        ///     y        <-- leftRotate(x) ---         x
        ///    / \                                    / \
        ///   x   c      --- rightRotate(y) -->      a   y
        ///  / \                                        / \
        /// a   b                                      b   c
        ///
        ///
        fn leftRotate(self: *Self, x: *Node) void {
            const y = x.right.?;

            // y to subtree root
            y.prev = x.prev;
            if (x.prev) |x_prev| {
                if (x_prev.left == x)
                    x_prev.left = y
                else
                    x_prev.right = y;
            } else {
                self.root = y;
            }

            x.right = y.left;
            if (y.left) |b| b.prev = x;

            x.prev = y;
            y.left = x;
        }

        fn rightRotate(self: *Self, y: *Node) void {
            const x = y.left.?;

            // x to subtree root
            x.prev = y.prev;
            if (y.prev) |y_prev| {
                if (y_prev.left == y)
                    y_prev.left = x
                else
                    y_prev.right = x;
            } else {
                self.root = x;
            }

            // b to y right
            y.left = x.right;
            if (x.right) |b| b.prev = y;

            // y to x right
            x.right = y;
            y.prev = x;
        }

        /// Remove node n from tree by giving node pointer.
        /// Sentinel node is inserted instead of null left/right node
        /// because removeBalance needs that extra sentinel node.
        pub fn remove(self: *Self, n: *Node) void {
            assert(self.root.? == n or (n.left != null or n.right != null or n.prev != null));
            defer n.clear();
            self.node_count -= 1;

            var original_color = n.color;
            var sentinel: Node = Node{ .color = .black, .left = null, .right = null, .prev = null, .key = undefined, .data = undefined };
            var x: *Node = &sentinel; // node to run removeBalance on it
            defer {
                if (original_color == .black)
                    self.removeBalance(x);
                if (x == &sentinel) { // remove sentinel if used during removeBalance
                    if (sentinel.prev) |prev| {
                        if (prev.left == &sentinel)
                            prev.left = null
                        else
                            prev.right = null;
                    }
                    if (self.root == &sentinel)
                        self.root = null;
                }
            }

            const left = n.left orelse {
                n.right = n.right orelse &sentinel;
                x = n.right.?;
                self.transplant(n, n.right);
                return;
            };
            const right = n.right orelse {
                n.left = n.left orelse &sentinel;
                x = n.left.?;
                self.transplant(n, n.left);
                return;
            };

            const y = right.minimum();
            original_color = y.color;
            y.right = y.right orelse &sentinel;
            x = y.right.?;
            if (y.prev == n) {
                x.prev = y;
            } else {
                self.transplant(y, y.right);
                y.right = right;
                right.prev = y;
            }
            self.transplant(n, y);
            y.left = left;
            left.prev = y;
            y.color = n.color;
        }

        /// Balance tree after node remove.
        fn removeBalance(self: *Self, n: *Node) void {
            var x = n;
            while (true) {
                if (x.color == .red) break;
                const prev = x.prev orelse break; // x.prev == null means root
                assert(prev.left != null and prev.right != null);
                if (x == prev.left) {
                    var w = prev.right.?;
                    if (w.color == .red) {
                        w.color = .black;
                        prev.color = .red;
                        self.leftRotate(prev);
                        w = prev.right.?;
                    }
                    if ((w.left == null or w.left.?.color == .black) and
                        (w.right == null or w.right.?.color == .black))
                    {
                        w.color = .red;
                        x = prev;
                        continue;
                    }
                    if (w.right == null or w.right.?.color == .black) {
                        w.left.?.color = .black;
                        w.color = .red;
                        self.rightRotate(w);
                        w = prev.right.?;
                    }
                    w.color = prev.color;
                    prev.color = .black;
                    w.right.?.color = .black;
                    self.leftRotate(prev);
                    break;
                } else {
                    var w = prev.left.?;
                    if (w.color == .red) {
                        w.color = .black;
                        prev.color = .red;
                        self.rightRotate(prev);
                        w = prev.left.?;
                    }
                    if ((w.right == null or w.right.?.color == .black) and
                        (w.left == null or w.left.?.color == .black))
                    {
                        w.color = .red;
                        x = prev;
                        continue;
                    }
                    if (w.left == null or w.left.?.color == .black) {
                        w.right.?.color = .black;
                        w.color = .red;
                        self.leftRotate(w);
                        w = prev.left.?;
                    }
                    w.color = prev.color;
                    prev.color = .black;
                    w.left.?.color = .black;
                    self.rightRotate(prev);
                    break;
                }
            }
            x.color = .black;
        }

        /// Transplant replaces the subtree rooted at node u with the subtree
        /// rooted at node v.
        fn transplant(self: *Self, u: *Node, v: ?*Node) void {
            const prev = u.prev orelse {
                // u was the root, replace it with v
                self.root = v;
                if (v) |vv| vv.prev = null;
                return;
            };
            if (u == prev.left)
                prev.left = v
            else
                prev.right = v;
            if (v) |vv| vv.prev = prev;
        }

        /// Number of nodes in the tree.
        pub fn count(self: *Self) usize {
            return self.node_count;
        }

        /// Assert red black tree invariants:
        ///   - root is black
        ///   - if node is red both children are black
        ///   - for each leaf node black depth (number of black nodes above) are the same
        fn assertInvariants(self: *Self) usize {
            const root = self.root orelse return 0;
            assert(root.color == .black);
            var tree_depth: usize = 0; // number of black nodes to the each leaf
            self.assertNodeInvariants(root, 0, &tree_depth);
            return tree_depth;
        }

        fn assertNodeInvariants(self: *Self, node: *Node, depth_: usize, tree_depth: *usize) void {
            var depth = depth_;
            if (node.color == .black)
                depth += 1;
            if (node.left) |left| {
                if (node.color == .red) // if node is red both children must be black
                    assert(left.color == .black);
                assert(left.prev == node);
                assert(compareFn(self.context, left.key, node.key) == .lt);
                self.assertNodeInvariants(left, depth, tree_depth);
            }
            if (node.right) |right| {
                if (node.color == .red) // if node is red both children must be black
                    assert(right.color == .black);
                assert(right.prev == node);
                assert(compareFn(self.context, right.key, node.key) == .gt);
                self.assertNodeInvariants(right, depth, tree_depth);
            }
            if (node.right == null and node.left == null) { // leaf node
                if (tree_depth.* == 0) // first leaf sets tree_depth
                    tree_depth.* = depth;
                assert(depth == tree_depth.*); // all other asserts same tree depth
            }
        }

        pub fn dot(self: *Self) bst.Dot(Self) {
            return .{ .tree = self };
        }

        /// Returns tree nodes iterator.
        /// Nodes are iterated in ascending key order.
        pub fn iter(self: *Self) Node.Iterator {
            return .{ .curr = self.minimum() };
        }

        // Preorder iterator visits root before any node in its subtrees.
        pub fn preorderIter(self: *Self) Node.PreorderIterator {
            return .{ .curr = self.root };
        }
    };
}

const testing = std.testing;

const compare = bst.compare;

test "left/right rotate" {
    const Tree = RedBlackTree(usize, void, void, compare(usize));
    const Node = Tree.Node;
    var t: Tree = .{ .context = {} };

    var x = Node{ .key = 1, .data = {} };
    var y = Node{ .key = 2, .data = {} };
    var a = Node{ .key = 3, .data = {} };
    var b = Node{ .key = 4, .data = {} };
    var c = Node{ .key = 5, .data = {} };

    y.left = &b;
    b.prev = &y;
    y.right = &c;
    c.prev = &y;
    x.left = &a;
    a.prev = &x;
    x.right = &y;
    y.prev = &x;
    t.root = &x;

    t.leftRotate(&x);

    try testing.expect(t.root == &y);
    try testing.expect(y.right == &c);
    try testing.expect(y.left == &x);
    try testing.expect(x.left == &a);
    try testing.expect(x.right == &b);

    t.rightRotate(&y);

    try testing.expect(t.root == &x);
    try testing.expect(x.left == &a);
    try testing.expect(x.right == &y);
    try testing.expect(y.left == &b);
    try testing.expect(y.right == &c);

    //t.printDotGraph();
}

const TestTreeFactory = struct {
    const alloc = testing.allocator;
    const Tree = RedBlackTree(usize, void, void, compare(usize));
    const Node = Tree.Node;

    tree: Tree,
    nodes: []Node,

    fn init(keys: []const usize) !TestTreeFactory {
        var nodes = try alloc.alloc(Node, keys.len);
        var tree = Tree{ .context = {} };
        for (keys, 0..) |v, i| {
            nodes[i] = .{ .key = v, .data = {} };
            var n = &nodes[i];
            tree.putNoClobber(n) catch unreachable;
            _ = tree.assertInvariants();
        }
        return .{
            .nodes = nodes,
            .tree = tree,
        };
    }
    fn deinit(self: *TestTreeFactory) void {
        alloc.free(self.nodes);
    }

    // returns node with key
    fn node(self: *TestTreeFactory, key: usize) *Node {
        for (self.nodes) |*n| {
            if (n.key == key)
                return n;
        }
        unreachable;
    }
};

const TestKeys = struct {
    const alloc = testing.allocator;
    keys: []usize,
    dp: std.rand.DefaultPrng = std.rand.DefaultPrng.init(0),

    fn init(len: usize) !TestKeys {
        var keys = try alloc.alloc(usize, len);
        for (keys, 0..) |*k, i| {
            k.* = i;
        }
        return .{
            .keys = keys,
        };
    }
    fn deinit(self: *TestKeys) void {
        alloc.free(self.keys);
    }
    fn shuffle(self: *TestKeys) void {
        self.dp.random().shuffle(usize, self.keys);
    }
};

// test "show keys" {
//     var tk = try TestKeys.init(10);
//     defer tk.deinit();

//     std.debug.print("{d}\n", .{tk.keys});
//     tk.shuffle();
//     std.debug.print("{d}\n", .{tk.keys});
//     tk.shuffle();
//     std.debug.print("{d}\n", .{tk.keys});
// }

test "rbt random create/remove" {
    var tk = try TestKeys.init(20);
    defer tk.deinit();

    for (0..1024) |_| { // test tree creation with 1024 random shuffles
        // create tree
        var ttf = try TestTreeFactory.init(tk.keys);
        defer ttf.deinit();
        var tree = ttf.tree;
        try testing.expect(tree.count() == tk.keys.len);
        try testing.expect(tree.assertInvariants() == 3);
        // remove from tree in random order
        tk.shuffle();
        for (tk.keys) |key| {
            tree.remove(ttf.node(key));
            try testing.expect(tree.assertInvariants() <= 3);
        }
        try testing.expect(tree.count() == 0);
        try testing.expect(tree.root == null);
    }
}

test "remove one node" {
    var tk = try TestKeys.init(128);
    defer tk.deinit();

    for (tk.keys) |key| {
        // create tree
        var ttf = try TestTreeFactory.init(tk.keys);
        defer ttf.deinit();
        var tree = ttf.tree;
        try testing.expect(tree.count() == tk.keys.len);
        // remove one node
        tree.remove(ttf.node(key));
        //try tree.dot().save("tmp/rbt_2.dot");

        try testing.expectEqual(@as(usize, 6), tree.assertInvariants());
        try testing.expect(tree.count() == tk.keys.len - 1);
    }
}

test "insert example from book" {
    var keys = [_]usize{ 11, 2, 14, 1, 7, 15, 5, 8 };
    var ttf = try TestTreeFactory.init(&keys);
    defer ttf.deinit();
    var tree = ttf.tree;
    try testing.expect(tree.root == ttf.node(11));
    // right tree
    try testing.expect(tree.root.?.right == ttf.node(14));
    try testing.expect(tree.root.?.right.?.color == .black);
    try testing.expect(tree.root.?.right.?.right == ttf.node(15));
    try testing.expect(tree.root.?.right.?.right.?.color == .red);
    // left tree
    try testing.expect(tree.root.?.left == ttf.node(2));
    try testing.expect(tree.root.?.left.?.color == .red);
    try testing.expect(tree.root.?.left.?.left == ttf.node(1));
    try testing.expect(tree.root.?.left.?.left.?.color == .black);
    try testing.expect(tree.root.?.left.?.right == ttf.node(7));
    try testing.expect(tree.root.?.left.?.right.?.color == .black);
    try testing.expect(tree.root.?.left.?.right.?.left == ttf.node(5));
    try testing.expect(tree.root.?.left.?.right.?.left.?.color == .red);
    try testing.expect(tree.root.?.left.?.right.?.right.?.color == .red);

    var n = TestTreeFactory.Node{ .key = 4, .data = {} };
    try tree.putNoClobber(&n);

    try testing.expect(tree.root == ttf.node(7));
    // right tree
    try testing.expect(tree.root.?.right == ttf.node(11));
    try testing.expect(tree.root.?.right.?.color == .red);
    try testing.expect(tree.root.?.right.?.left == ttf.node(8));
    try testing.expect(tree.root.?.right.?.left.?.color == .black);
    try testing.expect(tree.root.?.right.?.right == ttf.node(14));
    try testing.expect(tree.root.?.right.?.right.?.color == .black);
    try testing.expect(tree.root.?.right.?.right.?.right == ttf.node(15));
    try testing.expect(tree.root.?.right.?.right.?.right.?.color == .red);
    // left tree
    try testing.expect(tree.root.?.left == ttf.node(2));
    try testing.expect(tree.root.?.left.?.color == .red);
    try testing.expect(tree.root.?.left.?.left == ttf.node(1));
    try testing.expect(tree.root.?.left.?.left.?.color == .black);
    try testing.expect(tree.root.?.left.?.right == ttf.node(5));
    try testing.expect(tree.root.?.left.?.right.?.color == .black);
    try testing.expect(tree.root.?.left.?.right.?.left == &n);
    try testing.expect(tree.root.?.left.?.right.?.left.?.color == .red);

    try testing.expect(n.prev == ttf.node(5));
    try testing.expect(n.left == null);
    try testing.expect(n.right == null);
}

test "fetchPut" {
    var tk = try TestKeys.init(32);
    defer tk.deinit();
    var ttf = try TestTreeFactory.init(tk.keys);
    defer ttf.deinit();
    var tree = ttf.tree;

    var old = ttf.node(15);
    var new = TestTreeFactory.Node{ .key = 15, .data = {} };

    var removed = tree.fetchPut(&new);
    try testing.expect(removed.? == old);

    var n32 = TestTreeFactory.Node{ .key = 32, .data = {} };
    try testing.expect(tree.fetchPut(&n32) == null);

    try tree.dot().save("tmp/rbt_fetch_put.dot");
}
