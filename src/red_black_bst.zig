const std = @import("std");
const assert = std.debug.assert;

// Red-black binary search tree from Sedgewick Algorithms.
// BST with read and black *links* satisfying:
//  * red links lean left
//  * no node has two red links connected to it
//  * the tree has perfect black balanc: every path from the root to a null link
//  has the same number of black links

pub fn RedBlackBST(
    comptime T: type,
    comptime Context: type,
    comptime less: *const fn (ctx: Context, a: *T, b: *T) bool,
) type {
    return struct {
        const Self = @This();

        root: ?*T = null,
        context: Context,

        pub fn insert(self: *Self, n: *T) void {
            const root = self.insert_(self.root, n);
            root.tree.color = .black;
            self.root = root;
        }

        fn insert_(self: *Self, h_: ?*T, n: *T) *T {
            var h = h_ orelse return n;

            if (less(self.context, n, h)) {
                h.tree.left = self.insert_(h.tree.left, n);
            } else {
                h.tree.right = self.insert_(h.tree.right, n);
            }

            if (isRed(h.tree.right) and !isRed(h.tree.left)) h = leftRotate(h);
            if (isRed(h.tree.left) and isRed(h.tree.left.?.tree.left)) h = rightRotate(h);
            if (isRed(h.tree.left) and isRed(h.tree.right)) flipColors(h);

            return h;
        }

        fn isRed(n_: ?*T) bool {
            if (n_) |n| return n.tree.color == .red;
            return false;
        }

        /// Flip colors of two red children.
        ///
        ///       |                         ||
        ///       n                          n
        ///     // \\  --- flipColors -->   / \
        ///     l   r                      l   r
        ///
        ///  // = red       || = red
        ///   / = black      | = black
        ///
        fn flipColors(n: *T) void {
            assert(n.tree.right.?.tree.color == .red);
            assert(n.tree.left.?.tree.color == .red);

            n.tree.color = .red;
            n.tree.left.?.tree.color = .black;
            n.tree.right.?.tree.color = .black;
        }

        /// Left rotate y node with its parent .x node.
        /// Right rotate x node with it's parent y node.
        ///
        ///
        ///        |                                      |
        ///        y        <-- leftRotate(x) ---         x
        ///      // \                                    / \\
        ///      x   c      --- rightRotate(y) -->      a   y
        ///     / \                                        / \
        ///    a   b                                      b   c
        ///
        ///  y >= x
        ///  a < x
        ///  c >= y
        ///  y < b >= x
        fn leftRotate(x: *T) *T {
            const y = x.tree.right.?;
            assert(y.tree.color == .red);

            x.tree.right = y.tree.left;
            y.tree.left = x;

            y.tree.color = x.tree.color;
            x.tree.color = .red;
            return y;
        }

        fn rightRotate(y: *T) *T {
            const x = y.tree.left.?;
            assert(x.tree.color == .red);

            y.tree.left = x.tree.right;
            x.tree.right = y;

            x.tree.color = y.tree.color;
            y.tree.color = .red;
            return x;
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
            if (n.tree.left) |left| {
                print("\t{d} -> {d} [label=\"L\" color=\"{s}\"];\n", .{ n.value, left.value, left.tree.colorName() });
                printPointers(left);
            }
            if (n.tree.right) |right| {
                print("\t{d} -> {d} [label=\"R\" color=\"{s}\"];\n", .{ n.value, right.value, right.tree.colorName() });
                printPointers(right);
            }
        }
    };
}

const Color = enum {
    red,
    black,

    fn string(self: Color) []const u8 {
        return if (self == .red)
            "red"
        else
            "black";
    }
};

/// This should be set as the "tree" field in the type T.
pub fn Field(comptime T: type) type {
    return struct {
        left: ?*T = null,
        right: ?*T = null,
        color: Color = .red, // color of link from parent to this node

        fn colorName(self: *@This()) []const u8 {
            return self.color.string();
        }
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

test "left/right rotate" {
    const Tree = RedBlackBST(Node, void, Node.less);
    var t: Tree = .{ .context = {} };

    var x = Node{ .value = 2 };
    var y = Node{ .value = 4 };
    var a = Node{ .value = 1 };
    var b = Node{ .value = 3 };
    var c = Node{ .value = 5 };
    a.tree.color = .black;
    b.tree.color = .black;
    c.tree.color = .black;
    x.tree.color = .black;
    y.tree.color = .red;

    y.tree.left = &b;
    y.tree.right = &c;
    x.tree.left = &a;
    x.tree.right = &y;
    t.root = &x;

    t.root = Tree.leftRotate(&x);

    try testing.expect(t.root == &y);
    try testing.expect(y.tree.right == &c);
    try testing.expect(y.tree.left == &x);
    try testing.expect(x.tree.left == &a);
    try testing.expect(x.tree.right == &b);
    try testing.expect(x.tree.color == .red);
    try testing.expect(y.tree.color == .black);

    t.root = Tree.rightRotate(&y);

    try testing.expect(t.root == &x);
    try testing.expect(x.tree.left == &a);
    try testing.expect(x.tree.right == &y);
    try testing.expect(y.tree.left == &b);
    try testing.expect(y.tree.right == &c);
    try testing.expect(x.tree.color == .black);
    try testing.expect(y.tree.color == .red);

    //t.printDotGraph();
}

const TestTreeFactory = struct {
    const alloc = testing.allocator;
    const Tree = RedBlackBST(Node, void, Node.less);

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
    var ttf = try TestTreeFactory.init(&[_]usize{ 26, 17, 41, 14, 21, 30, 47, 10, 16, 19, 23, 28, 38, 7, 12, 15, 20, 35, 39, 3 });
    defer ttf.deinit();
    var tree = ttf.tree;

    tree.printDotGraph();
}
