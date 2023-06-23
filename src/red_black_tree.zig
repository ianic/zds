const std = @import("std");
const assert = std.debug.assert;
const Order = std.math.Order;
pub const bst = @import("binary_search_tree.zig");

const Error = bst.Error;

pub fn RedBlackTree(
    comptime K: type, // key data type
    comptime T: type, // value data type
    comptime Context: type,
    comptime compareFn: *const fn (ctx: Context, a: K, b: K) Order,
) type {
    return struct {
        const Color = enum {
            red,
            black,
        };

        /// Node inside the tree wrapping the actual data.
        pub const Node = struct {
            prev: ?*Node = null,
            left: ?*Node = null,
            right: ?*Node = null,
            color: Color = .red,

            key: K,
            data: T,
        };

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
                replace(x, n);
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
            assert(n.left == null and n.right == null and n.prev == null and n.color == .red);
            var x: *Node = self.root orelse {
                self.node_count = 1;
                n.color = .black;
                self.root = n;
                return null;
            };
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

        /// Replace old node o with new n.
        /// Old is removed from the tree.
        fn replace(o: *Node, n: *Node) void {
            n.left = o.left;
            n.right = o.right;
            n.prev = o.prev;
            n.color = o.color;
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
            n.color = .red;
        }

        /// Balance tree after putting node n.
        fn putBalance(self: *Self, n: *Node) void {
            var z = n;
            while (true) {
                const p = z.prev orelse break; // n is root
                if (p.color == .black) break;
                const pp = p.prev orelse break; // n is depth 1
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

        // /// Finds leaf node for inserting node n.
        // /// null if tree is empty, n should be root.
        // fn leafFor(self: *Self, n: *Node) ?*Node {
        //     var x: *T = self.root orelse return null;
        //     while (true) {
        //         x = if (less(self.context, n, x))
        //             x.left orelse return x
        //         else
        //             x.right orelse return x;
        //     }
        // }

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

        fn printDotGraph(self: *Self) !void {
            const root = self.root orelse return;
            const stdout = std.io.getStdOut().writer();

            try stdout.print("\ndigraph {{\n\tgraph [ordering=\"out\"];\n", .{});
            try printPointers(root);
            try stdout.print("}}\n", .{});
        }

        fn printPointers(n: *Node) !void {
            const stdout = std.io.getStdOut().writer();
            if (n.color == .red)
                try stdout.print("\t{d} [color=\"red\"];\n", .{n.key})
            else
                try stdout.print("\t{d} [color=\"black\"];\n", .{n.key});
            if (n.left) |left| {
                try stdout.print("\t{d} -> {d} [label=\"L\"];\n", .{ n.key, left.key });
                try printPointers(left);
            }
            if (n.right) |right| {
                try stdout.print("\t{d} -> {d} [label=\"R\"];\n", .{ n.key, right.key });
                try printPointers(right);
            }
        }
    };
}

const testing = std.testing;

pub const compare = bst.compare;

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

test "rbt random create" {
    var dp = std.rand.DefaultPrng.init(0);
    var rnd = dp.random();

    var keys = [_]usize{ 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20 };

    for (0..1024) |_| { // test tree creation with 1024 random shuffles
        var ttf = try TestTreeFactory.init(&keys);
        defer ttf.deinit();
        var tree = ttf.tree;
        try testing.expect(tree.count() == keys.len);
        try testing.expect(tree.assertInvariants() == 3);
        // if (i == 0)
        //     try tree.printDotGraph();
        rnd.shuffle(usize, &keys);
    }
}
