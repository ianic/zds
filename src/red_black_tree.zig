const std = @import("std");
const assert = std.debug.assert;

pub fn RedBlackTree(
    comptime T: type,
    comptime Context: type,
    comptime less: *const fn (ctx: Context, a: *T, b: *T) bool,
) type {
    return struct {
        const Self = @This();

        root: ?*T = null,
        context: Context,

        pub fn insert(self: *Self, n: *T) void {
            defer self.insertFixup(n);
            n.tree.color = .red;
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

        fn insertFixup(self: *Self, n: *T) void {
            var z = n;
            while (true) {
                const p = z.tree.prev orelse break; // n is root
                if (p.tree.color == .black) break;
                const pp = p.tree.prev orelse break; // n is depth 1
                if (p == pp.tree.left) {
                    const y = pp.tree.right orelse unreachable; // TODO
                    if (y.tree.color == .red) {
                        p.tree.color = .black;
                        y.tree.color = .black;
                        pp.tree.color = .red;
                        z = pp;
                        continue;
                    }
                    if (z == p.tree.right) {
                        z = p;
                        self.leftRotate(z);
                    }
                    if (z.tree.prev) |zp| {
                        zp.tree.color = .black;
                        if (zp.tree.prev) |zpp| {
                            zpp.tree.color = .red;
                            self.rightRotate(zpp);
                        }
                    }
                } else {
                    const y = pp.tree.left orelse unreachable; // TODO
                    if (y.tree.color == .red) {
                        p.tree.color = .black;
                        y.tree.color = .black;
                        pp.tree.color = .red;
                        z = pp;
                        continue;
                    }
                    if (z == p.tree.left) {
                        z = p;
                        self.rightRotate(z);
                    }
                    if (z.tree.prev) |zp| {
                        zp.tree.color = .black;
                        if (p.tree.prev) |zpp| {
                            zpp.tree.color = .red;
                            self.leftRotate(zpp);
                        }
                    }
                }
            }
            if (self.root) |root| root.tree.color = .black;
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
            const y = x.tree.right orelse return;

            // y to subtree root
            y.tree.prev = x.tree.prev;
            if (x.tree.prev) |x_prev| {
                if (x_prev.tree.left == x)
                    x_prev.tree.left = y
                else
                    x_prev.tree.right = y;
            } else {
                self.root = y;
            }

            x.tree.right = y.tree.left;
            if (y.tree.left) |b| b.tree.prev = x;

            x.tree.prev = y;
            y.tree.left = x;
        }

        fn rightRotate(self: *Self, y: *Node) void {
            const x = y.tree.left orelse return;

            // x to subtree root
            x.tree.prev = y.tree.prev;
            if (y.tree.prev) |y_prev| {
                if (y_prev.tree.left == y)
                    y_prev.tree.left = x
                else
                    y_prev.tree.right = x;
            } else {
                self.root = x;
            }

            // b to y right
            y.tree.left = x.tree.right;
            if (x.tree.right) |b|
                b.tree.prev = y;

            // y to x right
            x.tree.right = y;
            y.tree.prev = x;
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
            if (n.tree.color == .red)
                print("\t{d} [color=\"red\"];\n", .{n.value})
            else
                print("\t{d} [color=\"black\"];\n", .{n.value});
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

const Color = enum {
    red,
    black,
};

/// This should be set as the "tree" field in the type T.
pub fn Field(comptime T: type) type {
    return struct {
        left: ?*T = null,
        right: ?*T = null,
        prev: ?*T = null,
        color: Color = .red,
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

    fn setLeft(self: *Self, n: *Node) void {
        self.tree.left = n;
        n.tree.prev = self;
    }
    fn setRight(self: *Self, n: *Node) void {
        self.tree.right = n;
        n.tree.prev = self;
    }
};

test "left/right rotate" {
    const Rbt = RedBlackTree(Node, void, Node.less);
    var t: Rbt = .{ .context = {} };

    var x = Node{ .value = 1 };
    var y = Node{ .value = 2 };
    var a = Node{ .value = 3 };
    var b = Node{ .value = 4 };
    var c = Node{ .value = 5 };

    y.setLeft(&b);
    y.setRight(&c);
    x.setLeft(&a);
    x.setRight(&y);
    t.root = &x;

    t.leftRotate(&x);

    try testing.expect(t.root == &y);
    try testing.expect(y.tree.right == &c);
    try testing.expect(y.tree.left == &x);
    try testing.expect(x.tree.left == &a);
    try testing.expect(x.tree.right == &b);

    t.rightRotate(&y);

    try testing.expect(t.root == &x);
    try testing.expect(x.tree.left == &a);
    try testing.expect(x.tree.right == &y);
    try testing.expect(y.tree.left == &b);
    try testing.expect(y.tree.right == &c);

    //t.printDotGraph();
}

const TestTreeFactory = struct {
    const alloc = testing.allocator;
    const Tree = RedBlackTree(Node, void, Node.less);

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

test "insert" {
    var ttf = try TestTreeFactory.init(&[_]usize{ 11, 2, 14, 1, 7, 15, 5, 8, 4 });
    defer ttf.deinit();
    var tree = ttf.tree;

    tree.printDotGraph();
}

test "insert2" {
    var ttf = try TestTreeFactory.init(&[_]usize{ 26, 17, 41, 14, 21, 30, 47, 10, 16, 19, 23, 28, 38, 7, 12, 15, 20, 35, 39, 3 });
    defer ttf.deinit();
    var tree = ttf.tree;

    tree.printDotGraph();
}
