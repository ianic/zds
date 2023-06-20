const std = @import("std");
const assert = std.debug.assert;

const CompareResult = enum {
    less,
    equal,
    greater,
};

const Error = error{
    KeyExists,
};

pub fn BinarySearchTree(
    comptime K: type, // key data type
    comptime T: type, // value data type
    comptime Context: type,
    comptime compare: *const fn (ctx: Context, a: K, b: K) CompareResult,
) type {
    return struct {
        /// Node inside the tree wrapping the actual data.
        pub const Node = struct {
            prev: ?*Node = null,
            left: ?*Node = null,
            right: ?*Node = null,

            key: K,
            data: T,
        };

        const Self = @This();

        root: ?*Node = null,
        context: Context,

        /// Inserts a new `Node` into the tree, returning the previous one, if any.
        /// If node with the same key if found it is replaced with n and the previous is returned.
        /// So the caller has chance to deinit unused node.
        /// If key don't exists returns null.
        pub fn fetchPut(self: *Self, n: *Node) ?*Node {
            if (self.fetchPut_(n)) |x| {
                replace(x, n);
                return x;
            }
            return null;
        }

        //  Inserts node n into tree or returns existing one with the same key.
        fn fetchPut_(self: *Self, n: *Node) ?*Node {
            var x: *Node = self.root orelse {
                self.root = n;
                return null;
            };
            while (true) {
                x = switch (compare(self.context, n.key, x.key)) {
                    .less => x.left orelse {
                        x.left = n;
                        return null;
                    },
                    .greater => x.right orelse {
                        x.right = n;
                        return null;
                    },
                    .equal => {
                        return x;
                    },
                };
            }
        }

        /// Puts new node into tree if that key not exists.
        /// If the key is already in the tree returns error.
        pub fn putNoClobber(self: *Self, n: *Node) Error!void {
            if (self.fetchPut_(n)) |x| {
                assert(x.key == n.key);
                return Error.KeyExists;
            }
        }

        /// Replace old node o with new n.
        /// Old is removed from the tree.
        fn replace(o: *Node, n: *Node) void {
            n.left = o.left;
            n.right = o.right;
            n.prev = o.prev;
            if (o.prev) |prev| {
                if (prev.left == o)
                    prev.left = n
                else
                    prev.right = n;
            }
            if (o.left) |left| left.prev = n;
            if (o.right) |right| right.prev = n;
            clearPointers(o);
        }

        fn clearPointers(n: *Node) void {
            n.left = null;
            n.right = null;
            n.prev = null;
        }

        /// Get node by the key.
        /// Null if there is no node for that key.
        pub fn get(self: *Self, key: K) ?*Node {
            var x: *Node = self.root orelse {
                return null;
            };
            while (true) {
                x = switch (compare(self.context, key, x.key)) {
                    .less => x.left orelse {
                        return null;
                    },
                    .greater => x.right orelse {
                        return null;
                    },
                    .equal => {
                        return x;
                    },
                };
            }
        }

        pub fn contains(self: *Self, key: K) bool {
            return self.get(key) != null;
        }

        pub fn insert(self: *Self, n: *Node) void {
            var leaf = self.leafFor(n) orelse {
                self.root = n;
                return;
            };
            n.prev = leaf;
            if (compare(self.context, n.key, leaf.key) == .less) {
                leaf.left = n;
            } else {
                leaf.right = n;
            }
        }

        /// Finds leaf node for inserting node n.
        /// null if tree is empty, n should be root.
        fn leafFor(self: *Self, n: *Node) ?*Node {
            var x: *Node = self.root orelse return null;
            while (true) {
                x = if (compare(self.context, n.key, x.key) == .less)
                    x.left orelse return x
                else
                    x.right orelse return x;
            }
        }

        /// Assert binary search tree property:
        ///   - left node is less than parent
        ///   - right node is not less than parent
        fn assertInvariants(self: *Self, node: *Node) void {
            if (node.left) |left| {
                assert(left.prev == node);
                assert(compare(self.context, left.key, node.key) == .less);
                self.assertInvariants(left);
            }
            if (node.right) |right| {
                assert(right.prev == node);
                assert(compare(self.context, right.key, node.key) == .greater);
                self.assertInvariants(right);
            }
        }

        /// Minimum node in the tree or null if empty.
        pub fn minimum(self: *Self) ?*Node {
            var n: *Node = self.root orelse return null;
            while (true)
                n = n.left orelse return n;
        }

        pub fn minimumFor(n_: *Node) *Node {
            var n: *Node = n_;
            while (true)
                n = n.left orelse return n;
        }

        /// Maximum node in the tree or null if empty.
        pub fn maximum(self: *Self) ?*Node {
            var n = self.root orelse return null;
            while (true)
                n = n.right orelse return n;
        }

        pub fn maximumFor(n_: *Node) ?*Node {
            var n: *Node = n_;
            while (true)
                n = n.right orelse return n;
        }

        pub fn successor(self: *Self, n: *Node) ?*Node {
            _ = self;
            return successor_(n);
        }

        fn successor_(n: *Node) ?*Node {
            if (n.right) |right| return minimumFor(right);

            var prev = n;
            var curr = n.prev orelse return null;
            while (prev == curr.right) {
                prev = curr;
                curr = curr.prev orelse return null;
            }
            return curr;
        }

        fn predecessor(self: *Self, n: *Node) ?*Node {
            _ = self;
            return predecessor_(n);
        }

        fn predecessor_(n: *Node) ?*Node {
            if (n.left) |left| return maximumFor(left);

            var prev = n;
            var curr = n.prev orelse return null;
            while (prev == curr.left) {
                prev = curr;
                curr = curr.prev orelse return null;
            }
            return curr;
        }

        pub fn walk(
            self: *Self,
            comptime WalkContext: type,
            ctx: *WalkContext,
            comptime callback: *const fn (*WalkContext, *Node) void,
        ) void {
            nodeWalk(self.root, WalkContext, ctx, callback);
        }

        fn nodeWalk(
            node: ?*Node,
            comptime WalkContext: type,
            ctx: *WalkContext,
            comptime callback: *const fn (*WalkContext, *Node) void,
        ) void {
            if (node == null) return;
            const n = node.?;
            nodeWalk(n.left, WalkContext, ctx, callback);
            callback(ctx, n);
            nodeWalk(n.right, WalkContext, ctx, callback);
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
            defer clearPointers(n);
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
            const y = minimumFor(right);
            assert(y.left == null);
            self.transplant(y, y.right);
            self.transplant(n, y);

            y.left = left;
            left.prev = y;

            y.right = right;
            right.prev = y;
        }

        /// Transplant replaces the subtree rooted at node u with the subtree
        /// roted at node v.
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

        /// Print graphviz (dot) representation of the tree
        /// Example; call printDotGraph from test, remove stderr and create dot file from the stdout:
        /// $ zig test --test-filter fetchRemove binary_search_tree.zig 2>/dev/null > tree.dot
        fn printDotGraph(self: *Self) !void {
            const root = self.root orelse return;
            const stdout = std.io.getStdOut().writer();

            try stdout.print("\ndigraph {{\n\tgraph [ordering=\"out\"];\n", .{});
            try printPointers(root);
            try stdout.print("}}\n", .{});
        }

        fn printPointers(n: *Node) !void {
            const stdout = std.io.getStdOut().writer();
            if (n.left) |left| {
                try stdout.print("\t{d} -> {d} [label=\"L\" color=\"red\"];\n", .{ n.key, left.key });
                try printPointers(left);
            }
            if (n.right) |right| {
                try stdout.print("\t{d} -> {d} [label=\"R\" color=\"blue\"];\n", .{ n.key, right.key });
                try printPointers(right);
            }
        }

        const Iterator = struct {
            curr: ?*Node,

            pub fn next(self: *Iterator) ?*Node {
                var curr = self.curr orelse return null;
                self.curr = successor_(curr);
                return curr;
            }
        };

        pub fn iter(self: *Self) Iterator {
            return .{ .curr = self.minimum() };
        }
    };
}

const testing = std.testing;

// Less comparison for usize used in tests
fn testLess(ctx: void, a: usize, b: usize) CompareResult {
    _ = ctx;
    if (a < b) return .less;
    if (a > b) return .greater;
    return .equal;
}

// Produces test tree from the []const usize
const TestTreeFactory = struct {
    const alloc = testing.allocator;
    const Tree = BinarySearchTree(usize, void, void, testLess);
    const Node = Tree.Node;

    tree: Tree,
    nodes: []Node,

    fn init(values: []const usize) !TestTreeFactory {
        var nodes = try alloc.alloc(Node, values.len);
        var tree = Tree{ .context = {} };
        for (values, 0..) |v, i| {
            nodes[i] = .{ .key = v, .data = {} };
            tree.insert(&nodes[i]);
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
};

test "tree insert" {
    const Tree = BinarySearchTree(usize, void, void, testLess);
    var t: Tree = .{ .context = {} };

    var a = Tree.Node{ .key = 1, .data = {} };
    var b = Tree.Node{ .key = 2, .data = {} };
    var c = Tree.Node{ .key = 3, .data = {} };
    var d = Tree.Node{ .key = 4, .data = {} };

    try testing.expect(t.leafFor(&a) == null);
    t.insert(&c);
    try testing.expect(t.leafFor(&b) == &c);
    t.insert(&a);
    try testing.expect(t.leafFor(&b) == &a);
    t.insert(&d);
    try testing.expect(t.leafFor(&b) == &a);
    t.insert(&b);
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

    const Tree = BinarySearchTree(usize, void, void, testLess);
    var t: Tree = .{ .context = {} };

    const num_nodes: usize = 1024;
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
        t.insert(n);
    }
    t.assertInvariants(t.root.?);
    //t.printDotGraph();

    // delete in random order
    rnd.shuffle(*Tree.Node, nodes);
    for (nodes) |n| {
        t.assertInvariants(t.root.?);
        t.remove(n);
    }

    try testing.expect(t.root == null);
}

test "tree delete node" {
    const Tree = BinarySearchTree(usize, void, void, testLess);
    var t: Tree = .{ .context = {} };

    var q = Tree.Node{ .key = 1, .data = {} };
    var z = Tree.Node{ .key = 3, .data = {} };
    var l = Tree.Node{ .key = 2, .data = {} };
    var r = Tree.Node{ .key = 6, .data = {} };
    var y = Tree.Node{ .key = 4, .data = {} };
    var x = Tree.Node{ .key = 5, .data = {} };

    t.insert(&q);
    t.insert(&z);
    t.insert(&l);
    t.insert(&r);
    t.insert(&y);
    t.insert(&x);

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

    try testing.expect(Tree.minimumFor(&r) == &y);
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

    t.remove(&r);
    // after deleting x:
    //         q
    //          \
    //           l
    //
    try testing.expect(t.root.? == &q);
    try testing.expect(q.right.? == &l);

    t.remove(&l);
    // after deleting x:
    //         q
    //
    try testing.expect(t.root.? == &q);
    try testing.expect(q.right == null);
    try testing.expect(q.left == null);

    t.remove(&q);
    try testing.expect(t.root == null);
}

test "tree successor/predecessor" {
    var ttf = try TestTreeFactory.init(&[_]usize{ 15, 18, 17, 20, 6, 3, 7, 2, 4, 13, 9 });
    defer ttf.deinit();
    var tree = ttf.tree;
    try testing.expect(tree.successor(ttf.node(2)).?.key == 3);
    try testing.expect(tree.successor(ttf.node(3)).?.key == 4);
    try testing.expect(tree.successor(ttf.node(4)).?.key == 6);
    try testing.expect(tree.successor(ttf.node(6)).?.key == 7);
    try testing.expect(tree.successor(ttf.node(7)).?.key == 9);
    try testing.expect(tree.successor(ttf.node(9)).?.key == 13);
    try testing.expect(tree.successor(ttf.node(13)).?.key == 15);
    try testing.expect(tree.successor(ttf.node(15)).?.key == 17);
    try testing.expect(tree.successor(ttf.node(17)).?.key == 18);
    try testing.expect(tree.successor(ttf.node(18)).?.key == 20);
    try testing.expect(tree.successor(ttf.node(20)) == null);

    try testing.expect(tree.predecessor(ttf.node(2)) == null);
    try testing.expect(tree.predecessor(ttf.node(3)).?.key == 2);
    try testing.expect(tree.predecessor(ttf.node(4)).?.key == 3);
    try testing.expect(tree.predecessor(ttf.node(6)).?.key == 4);
    try testing.expect(tree.predecessor(ttf.node(7)).?.key == 6);
    try testing.expect(tree.predecessor(ttf.node(9)).?.key == 7);
    try testing.expect(tree.predecessor(ttf.node(13)).?.key == 9);
    try testing.expect(tree.predecessor(ttf.node(15)).?.key == 13);
    try testing.expect(tree.predecessor(ttf.node(17)).?.key == 15);
    try testing.expect(tree.predecessor(ttf.node(18)).?.key == 17);
    try testing.expect(tree.predecessor(ttf.node(20)).?.key == 18);
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
    var ttf = try TestTreeFactory.init(&[_]usize{ 15, 18, 17, 20, 6, 3, 7, 2, 4, 13, 9 });
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
    var ttf = try TestTreeFactory.init(&[_]usize{ 15, 18, 17, 20, 6, 3, 7, 2, 4, 13, 9 });
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
    var ttf = try TestTreeFactory.init(&[_]usize{ 15, 18, 17, 20, 6, 3, 7, 2, 4, 13, 9 });
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
