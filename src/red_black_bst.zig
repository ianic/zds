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

            if (isRed(h.tree.right) and !isRed(h.tree.left)) h = self.leftRotate(h);
            if (isRedAndLeftRed(h.tree.left)) h = self.rightRotate(h);
            if (isRed(h.tree.left) and isRed(h.tree.right)) flipColors(h);

            return h;
        }

        fn isRed(n_: ?*T) bool {
            if (n_) |n| return n.tree.color == .red;
            return false;
        }

        fn isRedAndLeftRed(n_: ?*T) bool {
            if (n_) |n| {
                if (n.tree.color == .red) {
                    if (n.tree.left) |left| {
                        return left.tree.color == .red;
                    }
                }
            }
            return false;
        }

        fn flipColors(n: *Node) void {
            n.tree.color = .red;
            if (n.tree.left) |left| left.tree.color = .black;
            if (n.tree.right) |right| right.tree.color = .black;
        }

        /// Left rotate x node with its parent (y node)
        ///
        ///
        ///        |                                      |
        ///        y        <-- leftRotate(x) ---         x
        ///  red->/ \                                    / \<-red
        ///      x   c      --- rightRotate(y) -->      a   y
        ///     / \                                        / \
        ///    a   b                                      b   c
        ///
        ///  y >= x
        ///  a < x
        ///  c >= y
        ///  y < b >= x
        fn leftRotate(self: *Self, x: *Node) *Node {
            const y = x.tree.right orelse return x;

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

            y.tree.color = x.tree.color;
            x.tree.color = .red;
            return y;
        }

        fn rightRotate(self: *Self, y: *Node) *Node {
            const x = y.tree.left orelse return y;

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
        prev: ?*T = null,
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
    const Rbt = RedBlackBST(Node, void, Node.less);
    var t: Rbt = .{ .context = {} };

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

    y.setLeft(&b);
    y.setRight(&c);
    x.setLeft(&a);
    x.setRight(&y);
    t.root = &x;

    _ = t.leftRotate(&x);

    try testing.expect(t.root == &y);
    try testing.expect(y.tree.right == &c);
    try testing.expect(y.tree.left == &x);
    try testing.expect(x.tree.left == &a);
    try testing.expect(x.tree.right == &b);
    try testing.expect(x.tree.color == .red);
    try testing.expect(y.tree.color == .black);

    _ = t.rightRotate(&y);

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
