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

        fn walk(self: *Self, comptime cb: *const fn (*T) void) void {
            nodeWalk(self.root, cb);
        }

        fn nodeWalk(node: ?*T, comptime cb: *const fn (*T) void) void {
            if (node == null) return;
            const n = node.?;
            nodeWalk(n.tree.left, cb);
            cb(n);
            nodeWalk(n.tree.right, cb);
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

test "tree basic operations" {
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

    const cb = struct {
        fn wrap(node: *Node) void {
            std.debug.print("{d}\n", .{node.value});
        }
    }.wrap;
    t.walk(cb);
}

test "tree random" {
    const alloc = testing.allocator;
    var dp = std.rand.DefaultPrng.init(0);
    var rnd = dp.random();

    const Tree = BinarySearchTree(Node, void, Node.less);
    var t: Tree = .{ .context = {} };

    const num_nodes: usize = 32;
    var elems = try alloc.alloc(Node, num_nodes);
    defer alloc.free(elems);

    var i: usize = 0;
    //var value: usize = 0;
    while (i < num_nodes) : (i += 1) {
        elems[i] = .{ .value = i };
    }

    rnd.shuffle(Node, elems);

    for (elems) |*elem| {
        t.insert(elem);
    }

    //printDotGraph(Node, t.root.?);
}

fn printDotGraph(comptime T: type, root: *T) void {
    const print = std.debug.print;
    print("\ndigraph {{\ngraph [ordering=\"out\"];", .{});
    printPointers(T, root, null);
    print("}}\n", .{});
}

fn printPointers(comptime T: type, e: *T, prev: ?*T) void {
    const print = std.debug.print;
    if (prev) |p| {
        if (e.tree.prev != p) {
            print("\t{d} -> {d} [label=\"prev missing\"];\n", .{ e.value, p.value });
            print("\t{d} -> {d} [label=\"prev\"];\n", .{ e.value, e.tree.prev.?.value });
        }
    }
    if (e.tree.left) |c| {
        print("\t{d} -> {d} [label=\"L\"];\n", .{ e.value, c.value });
        printPointers(T, c, e);
    }
    if (e.tree.right) |n| {
        print("\t{d} -> {d} [label=\"R\"];\n", .{ e.value, n.value });
        printPointers(T, n, e);
    }
}
