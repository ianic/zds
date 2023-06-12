const std = @import("std");
const assert = std.debug.assert;

pub fn BinarySearchTree(
    comptime T: type,
    comptime Context: type,
    comptime less: *const fn (ctx: Context, a: *T, b: *T) bool,
) type {
    return struct {
        const Self = @This();

        root: ?*T = null,
        context: Context,

        pub fn insert(self: *Self, n: *T) void {
            var leaf = self.leafFor(n) orelse {
                self.root = n;
                return;
            };
            n.tree.prev = leaf;
            if (less(self.context, n, leaf)) {
                leaf.tree.left = n;
            } else {
                leaf.tree.right = n;
            }
        }

        /// Finds leaf node for inserting node n.
        /// null if tree is empty, n should be root.
        fn leafFor(self: *Self, n: *T) ?*T {
            var x: *T = self.root orelse return null;
            while (true) {
                x = if (less(self.context, n, x))
                    x.tree.left orelse return x
                else
                    x.tree.right orelse return x;
            }
        }

        /// Assert binary search tree property:
        ///   - left node is less than parent
        ///   - right node is not less than parent
        fn assertValid(self: *Self, node: *T) void {
            if (node.tree.left) |left| {
                assert(left.tree.prev == node);
                assert(less(self.context, left, node));
                self.assertValid(left);
            }
            if (node.tree.right) |right| {
                assert(right.tree.prev == node);
                assert(!less(self.context, right, node));
                self.assertValid(right);
            }
        }

        /// Minimum node in the tree or null if empty.
        pub fn minimum(self: *Self) ?*T {
            var n: *T = self.root orelse return null;
            while (true)
                n = n.tree.left orelse return n;
        }

        pub fn minimumFor(n_: *T) *T {
            var n: *T = n_;
            while (true)
                n = n.tree.left orelse return n;
        }

        /// Maximum node in the tree or null if empty.
        pub fn maximum(self: *Self) ?*T {
            var n = self.root orelse return null;
            while (true)
                n = n.tree.right orelse return n;
        }

        pub fn maximumFor(n_: *T) ?*T {
            var n: *T = n_;
            while (true)
                n = n.tree.right orelse return n;
        }

        pub fn successor(self: *Self, n: *T) ?*T {
            _ = self;
            return successor_(n);
        }

        fn successor_(n: *T) ?*T {
            if (n.tree.right) |right| return minimumFor(right);

            var prev = n;
            var curr = n.tree.prev orelse return null;
            while (prev == curr.tree.right) {
                prev = curr;
                curr = curr.tree.prev orelse return null;
            }
            return curr;
        }

        fn predecessor(self: *Self, n: *T) ?*T {
            _ = self;
            return predecessor_(n);
        }

        fn predecessor_(n: *T) ?*T {
            if (n.tree.left) |left| return maximumFor(left);

            var prev = n;
            var curr = n.tree.prev orelse return null;
            while (prev == curr.tree.left) {
                prev = curr;
                curr = curr.tree.prev orelse return null;
            }
            return curr;
        }

        /// Search for the node in the tree with the same value as v node.
        /// Returns node from the tree, v is used in comparison only.
        pub fn search(self: *Self, v: *T) ?*T {
            var n: *T = self.root orelse return null;
            while (true) {
                if (less(self.context, v, n)) {
                    n = n.tree.left orelse return null;
                } else {
                    if (less(self.context, n, v)) {
                        n = n.tree.right orelse return null;
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
            comptime callback: *const fn (*WalkContext, *T) void,
        ) void {
            nodeWalk(self.root, WalkContext, ctx, callback);
        }

        fn nodeWalk(
            node: ?*T,
            comptime WalkContext: type,
            ctx: *WalkContext,
            comptime callback: *const fn (*WalkContext, *T) void,
        ) void {
            if (node == null) return;
            const n = node.?;
            nodeWalk(n.tree.left, WalkContext, ctx, callback);
            callback(ctx, n);
            nodeWalk(n.tree.right, WalkContext, ctx, callback);
        }

        /// Delete node z from tree
        pub fn delete(self: *Self, z: *T) void {
            const left = z.tree.left orelse {
                self.transplant(z, z.tree.right);
                return;
            };
            const right = z.tree.right orelse {
                self.transplant(z, z.tree.left);
                return;
            };
            if (right.tree.left == null) {
                self.transplant(z, right);
                left.tree.prev = right;
                right.tree.left = left;
                return;
            }
            const y = minimumFor(right);
            assert(y.tree.left == null);
            self.transplant(y, y.tree.right);
            self.transplant(z, y);

            y.tree.left = left;
            left.tree.prev = y;

            y.tree.right = right;
            right.tree.prev = y;
        }

        /// Transplant replaces the subtree rooted at node u with the subtree
        /// roted at node v.
        fn transplant(self: *Self, u: *T, v: ?*T) void {
            const prev = u.tree.prev orelse {
                // u was the root, replace it with v
                self.root = v;
                if (v) |vv| vv.tree.prev = null;
                return;
            };
            if (u == prev.tree.left)
                prev.tree.left = v
            else
                prev.tree.right = v;
            if (v) |vv| vv.tree.prev = prev;
        }

        fn printDotGraph(self: *Self) void {
            const root = self.root orelse return;
            const print = std.debug.print;
            print("\ndigraph {{\ngraph [ordering=\"out\"];", .{});
            printPointers(root);
            print("}}\n", .{});
        }

        fn printPointers(n: *T) void {
            const print = std.debug.print;
            // if (prev) |p| {
            //     if (e.tree.prev != p) {
            //         print("\t{d} -> {d} [label=\"prev missing\"];\n", .{ e.value, p.value });
            //         print("\t{d} -> {d} [label=\"prev\"];\n", .{ e.value, e.tree.prev.?.value });
            //     }
            // }
            if (n.tree.left) |left| {
                print("\t{d} -> {d} [label=\"L\"];\n", .{ n.value, left.value });
                printPointers(left);
            }
            if (n.tree.right) |right| {
                print("\t{d} -> {d} [label=\"R\"];\n", .{ n.value, right.value });
                printPointers(right);
            }
        }

        const Iterator = struct {
            curr: ?*T,

            pub fn next(self: *Iterator) ?*T {
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

/// The state that is required for IntrusiveHeap element types.
/// This should be set as the "tree" field in the type T.
pub fn Field(comptime T: type) type {
    return struct {
        left: ?*T = null,
        right: ?*T = null,
        prev: ?*T = null,
    };
}

const testing = std.testing;

// structure used in tests
const Node = struct {
    const Self = @This();
    value: usize = 0,
    tree: Field(Self) = .{},

    fn less(ctx: void, a: *Self, b: *Self) bool {
        _ = ctx;
        return a.value < b.value;
    }
};

test "tree basic operations insert/walk" {
    const Tree = BinarySearchTree(Node, void, Node.less);
    var t: Tree = .{ .context = {} };

    var a = Node{ .value = 1 };
    var b = Node{ .value = 2 };
    var c = Node{ .value = 3 };
    var d = Node{ .value = 4 };

    try testing.expect(t.leafFor(&b) == null);
    t.insert(&c);
    try testing.expect(t.leafFor(&b) == &c);
    t.insert(&a);
    try testing.expect(t.leafFor(&b) == &a);
    t.insert(&d);
    try testing.expect(t.leafFor(&b) == &a);
    t.insert(&b);
    t.assertValid(t.root.?);

    const Context = struct {
        values: [4]usize = undefined,
        idx: usize = 0,

        const Self = @This();
        fn callback(self: *Self, node: *Node) void {
            self.values[self.idx] = node.value;
            self.idx += 1;
            //std.debug.print("{d}\n", .{node.value});
        }
    };
    var ctx = Context{};
    t.walk(Context, &ctx, Context.callback);
    try testing.expectEqualSlices(usize, &[_]usize{ 1, 2, 3, 4 }, &ctx.values);

    try testing.expect(t.minimum().?.value == 1);
    try testing.expect(t.maximum().?.value == 4);

    var e = Node{ .value = 2 };
    try testing.expect(t.search(&e).? == &b);
    e.value = 4;
    try testing.expect(t.search(&e).? == &d);
    e.value = 5;
    try testing.expect(t.search(&e) == null);
}

test "tree random" {
    const alloc = testing.allocator;
    var dp = std.rand.DefaultPrng.init(0);
    var rnd = dp.random();

    const Tree = BinarySearchTree(Node, void, Node.less);
    var t: Tree = .{ .context = {} };

    const num_nodes: usize = 1024;
    var elems = try alloc.alloc(Node, num_nodes);
    var nodes = try alloc.alloc(*Node, num_nodes);
    defer alloc.free(elems);
    defer alloc.free(nodes);

    for (elems, 0..) |*elem, i| {
        elem.* = .{ .value = i };
        nodes[i] = elem;
    }

    // insert in random order
    rnd.shuffle(*Node, nodes);
    for (nodes) |elem| {
        t.insert(elem);
    }
    t.assertValid(t.root.?);
    //t.printDotGraph();

    // delete in random order
    rnd.shuffle(*Node, nodes);
    for (nodes) |elem| {
        t.assertValid(t.root.?);
        t.delete(elem);
    }

    try testing.expect(t.root == null);
}

test "tree delete node" {
    const Tree = BinarySearchTree(Node, void, Node.less);
    var t: Tree = .{ .context = {} };

    var q = Node{ .value = 1 };
    var z = Node{ .value = 3 };
    var l = Node{ .value = 2 };
    var r = Node{ .value = 6 };
    var y = Node{ .value = 4 };
    var x = Node{ .value = 5 };

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
    try testing.expect(q.tree.right.? == &z);
    try testing.expect(z.tree.left.? == &l);
    try testing.expect(z.tree.right.? == &r);
    try testing.expect(r.tree.left.? == &y);
    try testing.expect(y.tree.right.? == &x);
    t.assertValid(t.root.?);

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
    try testing.expect(q.tree.right.? == &y);
    try testing.expect(y.tree.left.? == &l);
    try testing.expect(y.tree.right.? == &r);
    try testing.expect(r.tree.left.? == &x);
    t.assertValid(t.root.?);

    t.delete(&y);
    // after deleting y:
    //         q
    //          \
    //           x
    //          / \
    //         l   r
    //
    try testing.expect(t.root.? == &q);
    try testing.expect(q.tree.right.? == &x);
    try testing.expect(x.tree.left.? == &l);
    try testing.expect(x.tree.right.? == &r);

    t.delete(&x);
    // after deleting x:
    //         q
    //          \
    //           r
    //          /
    //         l
    //
    try testing.expect(t.root.? == &q);
    try testing.expect(q.tree.right.? == &r);
    try testing.expect(r.tree.left.? == &l);

    t.delete(&r);
    // after deleting x:
    //         q
    //          \
    //           l
    //
    try testing.expect(t.root.? == &q);
    try testing.expect(q.tree.right.? == &l);

    t.delete(&l);
    // after deleting x:
    //         q
    //
    try testing.expect(t.root.? == &q);
    try testing.expect(q.tree.right == null);
    try testing.expect(q.tree.left == null);

    t.delete(&q);
    try testing.expect(t.root == null);
}

const TestTreeFactory = struct {
    const alloc = testing.allocator;
    const Tree = BinarySearchTree(Node, void, Node.less);

    tree: Tree,
    nodes: []Node,

    fn init(values: []const usize) !TestTreeFactory {
        var nodes = try alloc.alloc(Node, values.len);
        var tree = Tree{ .context = {} };
        for (values, 0..) |v, i| {
            nodes[i] = .{ .value = v };
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

    // returns node with value
    fn node(self: *TestTreeFactory, value: usize) *Node {
        for (self.nodes) |*n| {
            if (n.value == value)
                return n;
        }
        unreachable;
    }
};

test "tree successor/predecessor" {
    var ttf = try TestTreeFactory.init(&[_]usize{ 15, 18, 17, 20, 6, 3, 7, 2, 4, 13, 9 });
    defer ttf.deinit();
    var tree = ttf.tree;
    try testing.expect(tree.successor(ttf.node(2)).?.value == 3);
    try testing.expect(tree.successor(ttf.node(3)).?.value == 4);
    try testing.expect(tree.successor(ttf.node(4)).?.value == 6);
    try testing.expect(tree.successor(ttf.node(6)).?.value == 7);
    try testing.expect(tree.successor(ttf.node(7)).?.value == 9);
    try testing.expect(tree.successor(ttf.node(9)).?.value == 13);
    try testing.expect(tree.successor(ttf.node(13)).?.value == 15);
    try testing.expect(tree.successor(ttf.node(15)).?.value == 17);
    try testing.expect(tree.successor(ttf.node(17)).?.value == 18);
    try testing.expect(tree.successor(ttf.node(18)).?.value == 20);
    try testing.expect(tree.successor(ttf.node(20)) == null);

    try testing.expect(tree.predecessor(ttf.node(2)) == null);
    try testing.expect(tree.predecessor(ttf.node(3)).?.value == 2);
    try testing.expect(tree.predecessor(ttf.node(4)).?.value == 3);
    try testing.expect(tree.predecessor(ttf.node(6)).?.value == 4);
    try testing.expect(tree.predecessor(ttf.node(7)).?.value == 6);
    try testing.expect(tree.predecessor(ttf.node(9)).?.value == 7);
    try testing.expect(tree.predecessor(ttf.node(13)).?.value == 9);
    try testing.expect(tree.predecessor(ttf.node(15)).?.value == 13);
    try testing.expect(tree.predecessor(ttf.node(17)).?.value == 15);
    try testing.expect(tree.predecessor(ttf.node(18)).?.value == 17);
    try testing.expect(tree.predecessor(ttf.node(20)).?.value == 18);
}

test "tree iterator" {
    var values = [_]usize{ 15, 18, 17, 20, 6, 3, 7, 2, 4, 13, 9 };
    var ttf = try TestTreeFactory.init(&values);
    defer ttf.deinit();
    var tree = ttf.tree;

    var iter = tree.iter();
    std.sort.sort(usize, &values, {}, std.sort.asc(usize));
    for (values) |v| {
        try testing.expect(iter.next().?.value == v);
    }
    try testing.expect(iter.next() == null);
}
