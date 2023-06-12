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

        pub fn successor(n: *T) ?*T {
            if (n.tree.right) |r| return minimumFor(r);

            var y = n.tree.prev;
            var x = n;
            while (y != null and x == y.?.tree.right) {
                x = y.?;
                y = y.?.tree.prev;
            }
            return y;
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

test "tree successor" {
    const alloc = testing.allocator;
    const values = [_]usize{ 15, 18, 17, 20, 6, 3, 7, 2, 4, 13, 9 };

    const Tree = BinarySearchTree(Node, void, Node.less);
    var t: Tree = .{ .context = {} };

    var nodes = try alloc.alloc(Node, values.len);
    defer alloc.free(nodes);

    for (values, 0..) |v, i| {
        nodes[i] = .{ .value = v };
        t.insert(&nodes[i]);
    }
    try testing.expect(Tree.successor(&nodes[9]).?.value == 15);
}
