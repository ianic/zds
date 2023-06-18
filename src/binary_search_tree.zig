const std = @import("std");
const assert = std.debug.assert;

pub fn BinarySearchTree(
    comptime K: type, // key data type
    comptime T: type, // value data type
    comptime Context: type,
    comptime less: *const fn (ctx: Context, a: K, b: K) bool,
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

        pub fn insert(self: *Self, n: *Node) void {
            var leaf = self.leafFor(n) orelse {
                self.root = n;
                return;
            };
            n.prev = leaf;
            if (less(self.context, n.key, leaf.key)) {
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
                x = if (less(self.context, n.key, x.key))
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
                assert(less(self.context, left.key, node.key));
                self.assertInvariants(left);
            }
            if (node.right) |right| {
                assert(right.prev == node);
                assert(!less(self.context, right.key, node.key));
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

        /// Search for the node in the tree with the same value as v node.
        /// Returns node from the tree, v is used in comparison only.
        pub fn search(self: *Self, v: *Node) ?*Node {
            var n: *Node = self.root orelse return null;
            while (true) {
                if (less(self.context, v.key, n.key)) {
                    n = n.left orelse return null;
                } else {
                    if (less(self.context, n.key, v.key)) {
                        n = n.right orelse return null;
                    } else {
                        return n; // equal nodes
                    }
                }
            }
            return n;
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

        /// Delete node z from tree
        pub fn delete(self: *Self, z: *Node) void {
            const left = z.left orelse {
                self.transplant(z, z.right);
                return;
            };
            const right = z.right orelse {
                self.transplant(z, z.left);
                return;
            };
            if (right.left == null) {
                self.transplant(z, right);
                left.prev = right;
                right.left = left;
                return;
            }
            const y = minimumFor(right);
            assert(y.left == null);
            self.transplant(y, y.right);
            self.transplant(z, y);

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

        fn printDotGraph(self: *Self) void {
            const root = self.root orelse return;
            const print = std.debug.print;
            print("\ndigraph {{\ngraph [ordering=\"out\"];", .{});
            printPointers(root);
            print("}}\n", .{});
        }

        fn printPointers(n: *Node) void {
            const print = std.debug.print;
            if (n.left) |left| {
                print("\t{d} -> {d} [label=\"L\" color=\"red\"];\n", .{ n.key, left.key });
                printPointers(left);
            }
            if (n.right) |right| {
                print("\t{d} -> {d} [label=\"R\" color=\"blue\"];\n", .{ n.key, right.key });
                printPointers(right);
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
fn testLess(ctx: void, a: usize, b: usize) bool {
    _ = ctx;
    return a < b;
}

// Produces test tree from the []const usize
const TestTreeFactory = struct {
    const alloc = testing.allocator;
    const Tree = BinarySearchTree(usize, void, void, testLess);

    tree: Tree,
    nodes: []Tree.Node,

    fn init(values: []const usize) !TestTreeFactory {
        var nodes = try alloc.alloc(Tree.Node, values.len);
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
    fn find(self: *TestTreeFactory, key: usize) *Tree.Node {
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
        t.delete(n);
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
    t.delete(&z);
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

    t.delete(&y);
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

    t.delete(&x);
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

    t.delete(&r);
    // after deleting x:
    //         q
    //          \
    //           l
    //
    try testing.expect(t.root.? == &q);
    try testing.expect(q.right.? == &l);

    t.delete(&l);
    // after deleting x:
    //         q
    //
    try testing.expect(t.root.? == &q);
    try testing.expect(q.right == null);
    try testing.expect(q.left == null);

    t.delete(&q);
    try testing.expect(t.root == null);
}

test "tree successor/predecessor" {
    var ttf = try TestTreeFactory.init(&[_]usize{ 15, 18, 17, 20, 6, 3, 7, 2, 4, 13, 9 });
    defer ttf.deinit();
    var tree = ttf.tree;
    try testing.expect(tree.successor(ttf.find(2)).?.key == 3);
    try testing.expect(tree.successor(ttf.find(3)).?.key == 4);
    try testing.expect(tree.successor(ttf.find(4)).?.key == 6);
    try testing.expect(tree.successor(ttf.find(6)).?.key == 7);
    try testing.expect(tree.successor(ttf.find(7)).?.key == 9);
    try testing.expect(tree.successor(ttf.find(9)).?.key == 13);
    try testing.expect(tree.successor(ttf.find(13)).?.key == 15);
    try testing.expect(tree.successor(ttf.find(15)).?.key == 17);
    try testing.expect(tree.successor(ttf.find(17)).?.key == 18);
    try testing.expect(tree.successor(ttf.find(18)).?.key == 20);
    try testing.expect(tree.successor(ttf.find(20)) == null);

    try testing.expect(tree.predecessor(ttf.find(2)) == null);
    try testing.expect(tree.predecessor(ttf.find(3)).?.key == 2);
    try testing.expect(tree.predecessor(ttf.find(4)).?.key == 3);
    try testing.expect(tree.predecessor(ttf.find(6)).?.key == 4);
    try testing.expect(tree.predecessor(ttf.find(7)).?.key == 6);
    try testing.expect(tree.predecessor(ttf.find(9)).?.key == 7);
    try testing.expect(tree.predecessor(ttf.find(13)).?.key == 9);
    try testing.expect(tree.predecessor(ttf.find(15)).?.key == 13);
    try testing.expect(tree.predecessor(ttf.find(17)).?.key == 15);
    try testing.expect(tree.predecessor(ttf.find(18)).?.key == 17);
    try testing.expect(tree.predecessor(ttf.find(20)).?.key == 18);
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
