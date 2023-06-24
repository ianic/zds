const std = @import("std");
const assert = std.debug.assert;
const Order = std.math.Order;

pub const Error = error{
    KeyExists,
};

/// Node inside the tree wrapping the actual data.
pub fn BinarySearchTreeNode(
    comptime K: type,
    comptime T: type,
    comptime has_color: bool,
) type {
    return struct {
        const Node = @This();

        pub const Color = enum {
            red,
            black,
        };

        key: K,
        data: T,

        prev: ?*Node = null,
        left: ?*Node = null,
        right: ?*Node = null,
        color: if (has_color) Color else void = undefined,

        // Minimum in this node subtree.
        pub fn minimum(self: *Node) *Node {
            var n: *Node = self;
            while (true)
                n = n.left orelse return n;
        }

        // Maximum in this node subtree.
        pub fn maximum(self: *Node) *Node {
            var n: *Node = self;
            while (true)
                n = n.right orelse return n;
        }

        // Returns next node in ascending order.
        // Or null if node is last in tree ascending order.
        pub fn successor(self: *Node) ?*Node {
            // If the node has right edge next is minimum of its right subtree.
            if (self.right) |right| return right.minimum();

            // Go up all right edges.
            // Everything on the right is bigger so going up on the right edge gives smaller node.
            // Loop until found left edge to the parent and return that parent as next.
            var curr = self;
            while (true) {
                var prev = curr.prev orelse return null; // reached root, root.prev == null
                if (curr == prev.left) return prev; // reached prev from left edge => prev is bigger
                curr = prev;
            }
        }

        fn predecessor(self: *Node) ?*Node {
            if (self.left) |left| return left.maximum();

            var curr = self;
            while (true) {
                var prev = curr.prev orelse return null;
                if (curr == prev.right) return prev;
                curr = prev;
            }
        }

        // Returns next node for preorder tree walk.
        // Preorder tree walk visits root before any subtree.
        fn preoderNext(self: *Node) ?*Node {
            var curr = self;
            if (curr.left) |left| return left;
            if (curr.right) |right| return right;

            while (true) {
                var prev = curr.prev orelse return null;
                if (curr == prev.left) {
                    if (prev.right) |right| return right;
                    curr = prev;
                }
                curr = prev;
            }
        }

        /// Replace old node (self) with new n.
        /// Old is removed from the tree.
        fn replace(self: *Node, n: *Node) void {
            n.left = self.left;
            n.right = self.right;
            n.prev = self.prev;
            if (has_color)
                n.color = self.color;
            if (self.prev) |prev| {
                if (prev.left == self)
                    prev.left = n
                else
                    prev.right = n;
            }
            if (self.left) |left| left.prev = n;
            if (self.right) |right| right.prev = n;
            self.clear();
        }

        /// Clears node pointers.
        /// Node is no more member of a tree.
        pub fn clear(self: *Node) void {
            self.left = null;
            self.right = null;
            self.prev = null;
            if (has_color)
                self.color = .red;
        }

        fn writeEdges(self: *Node, comptime Writer: type, writer: Writer) !void {
            if (has_color)
                if (self.color == .red)
                    try writer.print("\t{d} [color=\"red\" fontcolor=\"red\"];\n", .{self.key});

            if (self.left) |left|
                try writeEdge(Writer, writer, self, left, "L", "green");
            if (self.right) |right|
                try writeEdge(Writer, writer, self, right, "R", "blue");
        }

        fn writeEdge(comptime Writer: type, writer: Writer, a: *Node, b: *Node, label: []const u8, color: []const u8) !void {
            try writer.print(
                "\t{d} -> {d} [label=\"{s}\" color=\"{s}\" fontcolor=\"{s}\" fontsize=9];\n",
                .{ a.key, b.key, label, color, color },
            );
            if (b.prev != a) {
                try writer.print(
                    "\t{d} -> {d} [label=\"P\" fontsize=9];\n",
                    .{ b.key, b.prev.?.key },
                );
            }
        }

        pub const Iterator = struct {
            curr: ?*Node,

            pub fn next(self: *Iterator) ?*Node {
                var curr = self.curr orelse return null;
                self.curr = curr.successor();
                return curr;
            }
        };

        pub const PreorderIterator = struct {
            curr: ?*Node,

            pub fn next(self: *PreorderIterator) ?*Node {
                var curr = self.curr orelse return null;
                self.curr = curr.preoderNext();
                return curr;
            }
        };
    };
}

pub fn BinarySearchTree(
    comptime K: type, // key data type
    comptime T: type, // value data type
    comptime Context: type,
    comptime compareFn: *const fn (ctx: Context, a: K, b: K) Order,
) type {
    return struct {
        pub const Node = BinarySearchTreeNode(K, T, false);

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
                self.root = n;
                return null;
            };
            while (true) {
                x = switch (compareFn(self.context, n.key, x.key)) {
                    .lt => x.left orelse {
                        self.node_count += 1;
                        n.prev = x;
                        x.left = n;
                        return null;
                    },
                    .gt => x.right orelse {
                        self.node_count += 1;
                        n.prev = x;
                        x.right = n;
                        return null;
                    },
                    .eq => {
                        return x;
                    },
                };
            }
        }

        /// Get node by the key.
        /// Null if there is no node for that key.
        pub fn get(self: *Self, key: K) ?*Node {
            var x: *Node = self.root orelse {
                return null;
            };
            while (true) {
                x = switch (compareFn(self.context, key, x.key)) {
                    .lt => x.left orelse {
                        return null;
                    },
                    .gt => x.right orelse {
                        return null;
                    },
                    .eq => {
                        return x;
                    },
                };
            }
        }

        pub fn contains(self: *Self, key: K) bool {
            return self.get(key) != null;
        }

        pub fn count(self: *Self) usize {
            return self.node_count;
        }

        /// Assert binary search tree property:
        ///   - left node is less than parent
        ///   - right node is greater less than parent
        ///   - prev points to parent
        fn assertInvariants(self: *Self, node: *Node) void {
            if (node.left) |left| {
                assert(left.prev == node);
                assert(compareFn(self.context, left.key, node.key) == .lt);
                self.assertInvariants(left);
            }
            if (node.right) |right| {
                assert(right.prev == node);
                assert(compareFn(self.context, right.key, node.key) == .gt);
                self.assertInvariants(right);
            }
        }

        /// Minimum node in the tree or null if empty.
        pub fn minimum(self: *Self) ?*Node {
            const root = self.root orelse return null;
            return root.minimum();
        }

        /// Maximum node in the tree or null if empty.
        pub fn maximum(self: *Self) ?*Node {
            const root = self.root orelse return null;
            return root.maximum()();
        }

        /// Remove node with key from the tree.
        /// Returns node so caller can deinit it.
        /// Returns null if key not in the tree.
        pub fn fetchRemove(self: *Self, key: K) ?*Node {
            if (self.get(key)) |n| {
                self.remove(n);
                return n;
            }
            return null;
        }

        /// Remove node n from tree by giving node pointer.
        pub fn remove(self: *Self, n: *Node) void {
            assert(self.root.? == n or (n.left != null or n.right != null or n.prev != null));
            defer n.clear();
            self.node_count -= 1;
            const left = n.left orelse {
                self.transplant(n, n.right);
                return;
            };
            const right = n.right orelse {
                self.transplant(n, n.left);
                return;
            };
            if (right.left == null) {
                self.transplant(n, right);
                left.prev = right;
                right.left = left;
                return;
            }
            const y = right.minimum();
            assert(y.left == null);
            self.transplant(y, y.right);
            self.transplant(n, y);

            y.left = left;
            left.prev = y;

            y.right = right;
            right.prev = y;
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

        pub fn dot(self: *Self) Dot(Self) {
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

/// Graphviz (dot) representation of the tree.
pub fn Dot(comptime Tree: type) type {
    return struct {
        const Self = @This();

        tree: *Tree,

        /// Print dot graph to the stdout.
        /// Can be used in tests to get graph on stdout. Test is writing to stderr so if we discard that we gat only dot.
        /// $ zig test --test-filter fetchRemove binary_search_tree.zig 2>/dev/null > tree.dot
        pub fn print(self: *const Self) !void {
            try self.write(std.fs.File.Writer, std.io.getStdOut().writer());
        }

        /// Actual dot graph writer.
        fn write(self: *const Self, comptime Writer: type, writer: Writer) !void {
            try writer.print("\ndigraph {{\n\tgraph [ordering=\"out\"];\n", .{});
            var it = self.tree.preorderIter();
            while (it.next()) |n| {
                try n.writeEdges(Writer, writer);
            }
            try writer.print("}}\n", .{});
        }

        /// Open file and write dot to the file.
        pub fn save(self: *const Self, path: []const u8) !void {
            var file = try std.fs.cwd().createFile(path, .{});
            try self.write(std.fs.File.Writer, file.writer());
            defer file.close();
        }
    };
}

/// Use to generate a comparator function for a given type: compare(usize)).
pub fn compare(comptime T: type) fn (void, T, T) Order {
    return struct {
        pub fn inner(_: void, a: T, b: T) Order {
            if (a < b) return .lt;
            if (a > b) return .gt;
            return .eq;
        }
    }.inner;
}

const testing = std.testing;

// Produces test tree from the []const usize
const TestTreeFactory = struct {
    const alloc = testing.allocator;
    const Tree = BinarySearchTree(usize, void, void, compare(usize));
    const Node = Tree.Node;

    tree: Tree,
    nodes: []Node,

    fn init(values: []const usize) !TestTreeFactory {
        var nodes = try alloc.alloc(Node, values.len);
        var tree = Tree{ .context = {} };
        for (values, 0..) |v, i| {
            nodes[i] = .{ .key = v, .data = {} };
            tree.putNoClobber(&nodes[i]) catch unreachable;
        }
        return .{
            .nodes = nodes,
            .tree = tree,
        };
    }

    fn deinit(self: *TestTreeFactory) void {
        alloc.free(self.nodes);
    }

    // Returns node by key
    fn node(self: *TestTreeFactory, key: usize) *Node {
        for (self.nodes) |*n| {
            if (n.key == key)
                return n;
        }
        unreachable;
    }

    // Returns default tree used in tests:
    //                 15
    //               /    \
    //              6     18
    //             / \    / \
    //            3   7  17  20
    //           / \   \
    //          2   4   13
    //                  /
    //                 9
    fn default() !TestTreeFactory {
        return try TestTreeFactory.init(&[_]usize{ 15, 18, 17, 20, 6, 3, 7, 2, 4, 13, 9 });
    }
};

test "tree insert" {
    const Tree = BinarySearchTree(usize, void, void, compare(usize));
    var t: Tree = .{ .context = {} };

    var a = Tree.Node{ .key = 1, .data = {} };
    var b = Tree.Node{ .key = 2, .data = {} };
    var c = Tree.Node{ .key = 3, .data = {} };
    var d = Tree.Node{ .key = 4, .data = {} };

    try testing.expect(t.count() == 0);
    try t.putNoClobber(&c);
    try testing.expect(t.count() == 1);
    try t.putNoClobber(&a);
    try testing.expect(t.count() == 2);
    try t.putNoClobber(&d);
    try testing.expect(t.count() == 3);
    try t.putNoClobber(&b);
    try testing.expect(t.count() == 4);
    t.assertInvariants(t.root.?);

    try testing.expect(t.root == &c);
    try testing.expect(c.left == &a);
    try testing.expect(c.right == &d);
    try testing.expect(a.left == null);
    try testing.expect(a.right == &b);
    try testing.expect(d.left == null);
    try testing.expect(d.right == null);

    //t.printDotGraph();
}

test "random insert/delete" {
    const alloc = testing.allocator;
    var dp = std.rand.DefaultPrng.init(0);
    var rnd = dp.random();

    const Tree = BinarySearchTree(usize, void, void, compare(usize));
    var t: Tree = .{ .context = {} };

    const num_nodes: usize = 128;
    var elems = try alloc.alloc(Tree.Node, num_nodes);
    var nodes = try alloc.alloc(*Tree.Node, num_nodes);
    defer alloc.free(elems);
    defer alloc.free(nodes);

    for (elems, 0..) |*elem, i| {
        elem.* = .{ .key = i, .data = {} };
        nodes[i] = elem;
    }

    // insert in random order
    rnd.shuffle(*Tree.Node, nodes);
    for (nodes) |n| {
        try t.putNoClobber(n);
    }
    t.assertInvariants(t.root.?);
    //try t.printDotGraph();

    // delete in random order
    rnd.shuffle(*Tree.Node, nodes);
    for (nodes) |n| {
        t.assertInvariants(t.root.?);
        t.remove(n);
    }

    try testing.expect(t.root == null);
}

test "tree delete node" {
    const Tree = BinarySearchTree(usize, void, void, compare(usize));
    var t: Tree = .{ .context = {} };

    var q = Tree.Node{ .key = 1, .data = {} };
    var z = Tree.Node{ .key = 3, .data = {} };
    var l = Tree.Node{ .key = 2, .data = {} };
    var r = Tree.Node{ .key = 6, .data = {} };
    var y = Tree.Node{ .key = 4, .data = {} };
    var x = Tree.Node{ .key = 5, .data = {} };

    try t.putNoClobber(&q);
    try t.putNoClobber(&z);
    try t.putNoClobber(&l);
    try t.putNoClobber(&r);
    try t.putNoClobber(&y);
    try t.putNoClobber(&x);

    // initial
    //         q
    //          \
    //           z
    //          / \
    //         l   r
    //            /
    //           y
    //            \
    //             x
    //
    try testing.expect(t.root.? == &q);
    try testing.expect(q.right.? == &z);
    try testing.expect(z.left.? == &l);
    try testing.expect(z.right.? == &r);
    try testing.expect(r.left.? == &y);
    try testing.expect(y.right.? == &x);
    t.assertInvariants(t.root.?);
    try testing.expect(t.count() == 6);

    try testing.expect(r.minimum() == &y);
    t.remove(&z);
    //printDotGraph(Node, t.root.?);

    // after deleting z:
    //         q
    //          \
    //           y
    //          / \
    //         l   r
    //            /
    //           x
    //
    try testing.expect(t.root.? == &q);
    try testing.expect(q.right.? == &y);
    try testing.expect(y.left.? == &l);
    try testing.expect(y.right.? == &r);
    try testing.expect(r.left.? == &x);
    t.assertInvariants(t.root.?);
    try testing.expect(t.count() == 5);

    t.remove(&y);
    // after deleting y:
    //         q
    //          \
    //           x
    //          / \
    //         l   r
    //
    try testing.expect(t.root.? == &q);
    try testing.expect(q.right.? == &x);
    try testing.expect(x.left.? == &l);
    try testing.expect(x.right.? == &r);
    try testing.expect(t.count() == 4);

    t.remove(&x);
    // after deleting x:
    //         q
    //          \
    //           r
    //          /
    //         l
    //
    try testing.expect(t.root.? == &q);
    try testing.expect(q.right.? == &r);
    try testing.expect(r.left.? == &l);
    try testing.expect(t.count() == 3);

    t.remove(&r);
    // after deleting x:
    //         q
    //          \
    //           l
    //
    try testing.expect(t.root.? == &q);
    try testing.expect(q.right.? == &l);
    try testing.expect(t.count() == 2);

    t.remove(&l);
    // after deleting x:
    //         q
    //
    try testing.expect(t.root.? == &q);
    try testing.expect(q.right == null);
    try testing.expect(q.left == null);
    try testing.expect(t.count() == 1);

    t.remove(&q);
    try testing.expect(t.root == null);
    try testing.expect(t.count() == 0);
}

test "tree successor/predecessor" {
    var ttf = try TestTreeFactory.default();
    defer ttf.deinit();

    try testing.expect(ttf.node(2).successor().?.key == 3);
    try testing.expect(ttf.node(3).successor().?.key == 4);
    try testing.expect(ttf.node(4).successor().?.key == 6);
    try testing.expect(ttf.node(6).successor().?.key == 7);
    try testing.expect(ttf.node(7).successor().?.key == 9);
    try testing.expect(ttf.node(9).successor().?.key == 13);
    try testing.expect(ttf.node(13).successor().?.key == 15);
    try testing.expect(ttf.node(15).successor().?.key == 17);
    try testing.expect(ttf.node(17).successor().?.key == 18);
    try testing.expect(ttf.node(18).successor().?.key == 20);
    try testing.expect(ttf.node(20).successor() == null);

    try testing.expect(ttf.node(2).predecessor() == null);
    try testing.expect(ttf.node(3).predecessor().?.key == 2);
    try testing.expect(ttf.node(4).predecessor().?.key == 3);
    try testing.expect(ttf.node(6).predecessor().?.key == 4);
    try testing.expect(ttf.node(7).predecessor().?.key == 6);
    try testing.expect(ttf.node(9).predecessor().?.key == 7);
    try testing.expect(ttf.node(13).predecessor().?.key == 9);
    try testing.expect(ttf.node(15).predecessor().?.key == 13);
    try testing.expect(ttf.node(17).predecessor().?.key == 15);
    try testing.expect(ttf.node(18).predecessor().?.key == 17);
    try testing.expect(ttf.node(20).predecessor().?.key == 18);
}

test "tree iterator" {
    var values = [_]usize{ 15, 18, 17, 20, 6, 3, 7, 2, 4, 13, 9 };
    var ttf = try TestTreeFactory.init(&values);
    defer ttf.deinit();
    var tree = ttf.tree;

    // expect that iterator returns sorted values
    var iter = tree.iter();
    std.sort.sort(usize, &values, {}, std.sort.asc(usize));
    for (values) |v| {
        try testing.expect(iter.next().?.key == v);
    }
    try testing.expect(iter.next() == null);
}

test "fetchPut" {
    var ttf = try TestTreeFactory.default();
    defer ttf.deinit();
    var tree = ttf.tree;
    const Node = TestTreeFactory.Node;

    var n16 = Node{ .key = 16, .data = {} }; // does not exists
    try testing.expect(tree.fetchPut(&n16) == null);

    var n6 = Node{ .key = 6, .data = {} }; // already exists in the tree

    // putting existing node returns old with that key
    const o6 = tree.fetchPut(&n6).?;
    try testing.expect(o6.key == 6);
    try testing.expect(o6 != &n6);

    // putNoClobber of existing node returns error
    var n9 = Node{ .key = 9, .data = {} }; // already exists in the tree
    try testing.expect(tree.putNoClobber(&n9) == Error.KeyExists);

    // putNoClobber when that key don't exists
    var n8 = Node{ .key = 8, .data = {} };
    try tree.putNoClobber(&n8);
}

test "get/contains" {
    var ttf = try TestTreeFactory.default();
    defer ttf.deinit();
    var tree = ttf.tree;

    try testing.expect(tree.get(0) == null);
    try testing.expect(tree.get(13).? == ttf.node(13));
    try testing.expect(tree.get(18).? == ttf.node(18));

    try testing.expect(!tree.contains(0));
    try testing.expect(tree.contains(13));
    try testing.expect(tree.contains(17));
}

test "remove/fetchRemove" {
    var ttf = try TestTreeFactory.default();
    defer ttf.deinit();
    var tree = ttf.tree;
    try testing.expect(tree.root.?.left.?.key == 6);

    try testing.expect(tree.fetchRemove(0) == null);

    const n6 = tree.fetchRemove(6).?;
    try testing.expect(n6.key == 6);
    try testing.expect(n6.prev == null);
    try testing.expect(n6.left == null);
    try testing.expect(n6.right == null);
    tree.assertInvariants(tree.root.?);

    try testing.expect(tree.root.?.left.?.key == 7);
}

test "preorder iterator" {
    var ttf = try TestTreeFactory.default();
    defer ttf.deinit();
    var tree = ttf.tree;

    const p_expected = [_]usize{ 15, 6, 3, 2, 4, 7, 13, 9, 18, 17, 20 };
    var p_iter = tree.preorderIter();
    var i: usize = 0;
    while (p_iter.next()) |n| {
        try testing.expect(n.key == p_expected[i]);
        i += 1;
    }

    const expected = [_]usize{ 2, 3, 4, 6, 7, 9, 13, 15, 17, 18, 20 };
    var iter = tree.iter();
    i = 0;
    while (iter.next()) |n| {
        try testing.expect(n.key == expected[i]);
        i += 1;
    }
    //try tree.dot().print();
    try tree.dot().save("tmp/test.dot");
}

// test "are they same size" {
//     const BST = BinarySearchTree(usize, void, void, compare(usize));
//     const ColorNode = BinarySearchTreeNode(usize, void, true);
//     std.debug.print("Node size: {d} {d}\n", .{ @sizeOf(BST.Node), @bitSizeOf(BST.Node) });
//     std.debug.print("Node2 size: {d} {d}\n", .{ @sizeOf(BST.Node2), @bitSizeOf(BST.Node2) });
//     std.debug.print("ColorNode size: {d} {d}\n", .{ @sizeOf(ColorNode), @bitSizeOf(ColorNode) });
// }
