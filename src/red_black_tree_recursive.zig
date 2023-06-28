const std = @import("std");
const assert = std.debug.assert;
const Order = std.math.Order;
const main = @import("main.zig");

const compare = main.compare;
const Error = main.Error;

// Red-black binary search tree from Sedgewick Algorithms book.
// BST with read and black *links* satisfying:
//  * red links lean left
//  * no node has two red links connected to it
//  * the tree has perfect black balance: every path from the root to a null link
//  has the same number of black links
// This uses recursive insert implementation.
//
// TODO:
// * deletion

pub fn RedBlackBST(
    comptime K: type, // key data type
    comptime T: type, // value data type
    comptime Context: type,
    comptime compareFn: *const fn (ctx: Context, a: K, b: K) Order,
) type {
    return struct {
        const Self = @This();

        const Node = struct {
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

            left: ?*Node = null,
            right: ?*Node = null,
            color: Color = .red, // color of link from parent to this node

            key: K,
            data: T,

            fn colorName(self: *@This()) []const u8 {
                return self.color.string();
            }
        };

        root: ?*Node = null,
        context: Context,
        node_count: usize = 0,

        /// Inserts a new `Node` into the tree, returning the previous one, if any.
        /// If node with the same key if found it is replaced with n and the previous is returned.
        /// So the caller has chance to deinit unused node.
        /// If key don't exists returns null.
        pub fn fetchPut(self: *Self, n: *Node) ?*Node {
            self.putNoClober(n) catch {
                // putNoClobber failed means node with same key as node n exists
                // find that node in x, and previous of x in prev
                var x = self.root.?;
                var prev: ?*Node = null;

                while (true) {
                    switch (compareFn(self.context, n.key, x.key)) {
                        .lt => {
                            prev = x;
                            x = x.left.?;
                        },
                        .gt => {
                            prev = x;
                            x = x.right.?;
                        },
                        .eq => { //found node n with same key as node n
                            // replace prev left/right with n
                            if (prev) |p| {
                                if (p.left == x) {
                                    p.left = n;
                                } else {
                                    p.right = n;
                                }
                            } else {
                                // or if prev == null the x is root
                                self.root = n;
                            }
                            // set n pointers to x pointers
                            n.left = x.left;
                            n.right = x.right;
                            n.color = x.color;
                            // delete x pointers
                            x.left = null;
                            x.right = null;
                            x.color = .red;
                            return x;
                        },
                    }
                }
            };
            return null;
        }

        /// Puts new node into tree if that key not exists.
        /// If the key is already in the tree returns error.
        pub fn putNoClober(self: *Self, n: *Node) Error!void {
            assert(n.left == null and n.right == null and n.color == .red);
            const root = try self.insert_(self.root, n);
            root.color = .black;
            self.node_count += 1;
            self.root = root;
        }

        fn insert_(self: *Self, h_: ?*Node, n: *Node) Error!*Node {
            var h = h_ orelse return n;

            switch (compareFn(self.context, n.key, h.key)) {
                .lt => h.left = try self.insert_(h.left, n),
                .gt => h.right = try self.insert_(h.right, n),
                .eq => return Error.KeyExists,
            }

            if (isRed(h.right) and !isRed(h.left)) h = leftRotate(h);
            if (isRed(h.left) and isRed(h.left.?.left)) h = rightRotate(h);
            if (isRed(h.left) and isRed(h.right)) flipColors(h);

            return h;
        }

        fn isRed(n_: ?*Node) bool {
            if (n_) |n| return n.color == .red;
            return false;
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

        pub fn count(self: *Self) usize {
            return self.node_count;
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
        fn flipColors(n: *Node) void {
            assert(n.right.?.color == .red);
            assert(n.left.?.color == .red);

            n.color = .red;
            n.left.?.color = .black;
            n.right.?.color = .black;
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
        fn leftRotate(x: *Node) *Node {
            const y = x.right.?;
            assert(y.color == .red);

            x.right = y.left;
            y.left = x;

            y.color = x.color;
            x.color = .red;
            return y;
        }

        fn rightRotate(y: *Node) *Node {
            const x = y.left.?;
            assert(x.color == .red);

            y.left = x.right;
            x.right = y;

            x.color = y.color;
            y.color = .red;
            return x;
        }

        pub fn dot(self: *Self) Dot(Self) {
            return .{ .tree = self };
        }

        // Check tree structure regarding three rules:
        //  * root is black
        //  * red links lean left
        //  * all leaf nodes have same red link depth
        // Returns tree depth, number of black links to the leaf.
        // Must be same for all leaf nodes (checkNode asserts that).
        fn assertInvariants(self: *Self) usize {
            const root = self.root orelse return 0;
            assert(root.color == .black);
            var tree_depth: usize = 0;
            assertNode(root, 0, &tree_depth);
            return tree_depth;
        }

        fn assertNode(n: *Node, depth: usize, tree_depth: *usize) void {
            if (n.right) |right| {
                assert(right.color == .black); // red links only on the left
                assertNode(right, depth + 1, tree_depth);
            }
            if (n.left) |left| {
                if (left.color == .red)
                    assertNode(left, depth, tree_depth)
                else
                    assertNode(left, depth + 1, tree_depth);
            }
            if (n.left == null and n.right == null) { // leaf node
                if (tree_depth.* == 0)
                    tree_depth.* = depth; // first leaft sets tree_depth
                assert(depth == tree_depth.*); // all others must be equal
            }
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
            if (self.tree.root) |root|
                try self.writeNode(Writer, writer, root);
            try writer.print("}}\n", .{});
        }

        fn writeNode(self: *const Self, comptime Writer: type, writer: Writer, n: *Tree.Node) !void {
            if (n.left) |left| {
                try writer.print("\t{d} -> {d} [label=\"L\" color=\"{s}\" fontsize=9];\n", .{ n.key, left.key, left.colorName() });
                try self.writeNode(Writer, writer, left);
            }
            if (n.right) |right| {
                try writer.print("\t{d} -> {d} [label=\"R\" color=\"{s}\" fontsize=9];\n", .{ n.key, right.key, right.colorName() });
                try self.writeNode(Writer, writer, right);
            }
        }

        /// Open file and write dot to the file.
        pub fn save(self: *const Self, path: []const u8) !void {
            var file = try std.fs.cwd().createFile(path, .{});
            try self.write(std.fs.File.Writer, file.writer());
            defer file.close();
        }
    };
}

const testing = std.testing;

test "left/right rotate" {
    const Tree = RedBlackBST(usize, void, void, compare(usize));
    var t: Tree = .{ .context = {} };

    var x = Tree.Node{ .key = 2, .data = {} };
    var y = Tree.Node{ .key = 4, .data = {} };
    var a = Tree.Node{ .key = 1, .data = {} };
    var b = Tree.Node{ .key = 3, .data = {} };
    var c = Tree.Node{ .key = 5, .data = {} };
    a.color = .black;
    b.color = .black;
    c.color = .black;
    x.color = .black;
    y.color = .red;

    y.left = &b;
    y.right = &c;
    x.left = &a;
    x.right = &y;
    t.root = &x;

    t.root = Tree.leftRotate(&x);

    try testing.expect(t.root == &y);
    try testing.expect(y.right == &c);
    try testing.expect(y.left == &x);
    try testing.expect(x.left == &a);
    try testing.expect(x.right == &b);
    try testing.expect(x.color == .red);
    try testing.expect(y.color == .black);

    t.root = Tree.rightRotate(&y);

    try testing.expect(t.root == &x);
    try testing.expect(x.left == &a);
    try testing.expect(x.right == &y);
    try testing.expect(y.left == &b);
    try testing.expect(y.right == &c);
    try testing.expect(x.color == .black);
    try testing.expect(y.color == .red);

    //t.printDotGraph();
}

const TestTreeFactory = struct {
    const alloc = testing.allocator;
    const Tree = RedBlackBST(usize, void, void, compare(usize));
    const Node = Tree.Node;

    tree: Tree,
    nodes: []Node,

    fn init(values: []const usize) !TestTreeFactory {
        var nodes = try alloc.alloc(Node, values.len);
        var tree = Tree{ .context = {} };
        for (values, 0..) |v, i| {
            nodes[i] = .{ .key = v, .data = {} };
            try tree.putNoClober(&nodes[i]);
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

test "insert into single 3 node case 1 larger" {
    const Tree = RedBlackBST(usize, void, void, compare(usize));
    const Node = Tree.Node;
    var t: Tree = .{ .context = {} };

    var a = Node{ .key = 1, .data = {} };
    var b = Node{ .key = 2, .data = {} };
    try t.putNoClober(&a);
    try t.putNoClober(&b);
    try testing.expect(t.root.? == &b);
    try testing.expect(b.color == .black);
    try testing.expect(a.color == .red);
    try testing.expect(b.left == &a);

    var c = Node{ .key = 3, .data = {} };
    try t.putNoClober(&c);
    try testing.expect(t.root.? == &b);
    try testing.expect(a.color == .black);
    try testing.expect(b.color == .black);
    try testing.expect(c.color == .black);
    try testing.expect(b.left == &a);
    try testing.expect(b.right == &c);
}

test "insert into single 3 node case 2 smaller" {
    const Tree = RedBlackBST(usize, void, void, compare(usize));
    const Node = Tree.Node;
    var t: Tree = .{ .context = {} };

    var b = Node{ .key = 2, .data = {} };
    var c = Node{ .key = 3, .data = {} };
    try t.putNoClober(&b);
    try t.putNoClober(&c);
    try testing.expect(t.root.? == &c);
    try testing.expect(c.color == .black);
    try testing.expect(b.color == .red);
    try testing.expect(c.left == &b);

    var a = Node{ .key = 1, .data = {} };
    try t.putNoClober(&a);
    try testing.expect(t.root.? == &b);
    try testing.expect(a.color == .black);
    try testing.expect(b.color == .black);
    try testing.expect(c.color == .black);
    try testing.expect(b.left == &a);
    try testing.expect(b.right == &c);
}

test "insert into single 3 node case 3 between" {
    const Tree = RedBlackBST(usize, void, void, compare(usize));
    const Node = Tree.Node;
    var t: Tree = .{ .context = {} };

    var a = Node{ .key = 1, .data = {} };
    var c = Node{ .key = 3, .data = {} };
    try t.putNoClober(&a);
    try t.putNoClober(&c);
    try testing.expect(t.root.? == &c);
    try testing.expect(c.color == .black);
    try testing.expect(a.color == .red);
    try testing.expect(c.left == &a);

    var b = Node{ .key = 2, .data = {} };
    try t.putNoClober(&b);
    try testing.expect(t.root.? == &b);
    try testing.expect(a.color == .black);
    try testing.expect(b.color == .black);
    try testing.expect(c.color == .black);
    try testing.expect(b.left == &a);
    try testing.expect(b.right == &c);
}

test "insert into 3 node at the bottom" {
    const Tree = RedBlackBST(usize, void, void, compare(usize));
    const Node = Tree.Node;
    var t: Tree = .{ .context = {} };

    var e = Node{ .key = 'e', .data = {} };
    var c = Node{ .key = 'c', .data = {} };
    var a = Node{ .key = 'a', .data = {} };
    var s = Node{ .key = 's', .data = {} };
    var r = Node{ .key = 'r', .data = {} };
    try t.putNoClober(&c);
    try t.putNoClober(&e);
    try t.putNoClober(&s);
    try t.putNoClober(&r);
    try t.putNoClober(&a);
    //       e
    //      / \
    //     c   s
    //    //  //
    //   a    r
    try testing.expect(t.root.? == &e);
    try testing.expect(e.left == &c);
    try testing.expect(e.right == &s);
    try testing.expect(c.left == &a);
    try testing.expect(s.left == &r);
    try testing.expect(e.color == .black);
    try testing.expect(c.color == .black);
    try testing.expect(s.color == .black);
    try testing.expect(a.color == .red);
    try testing.expect(r.color == .red);
    try testing.expect(t.assertInvariants() == 1);

    var h = Node{ .key = 'h', .data = {} };
    try t.putNoClober(&h);
    //       r
    //      //\
    //     e   s
    //    / \
    //   c   h
    //  //
    //  a
    try testing.expect(t.root.? == &r);
    try testing.expect(r.left == &e);
    try testing.expect(r.right == &s);
    try testing.expect(e.left == &c);
    try testing.expect(e.right == &h);
    try testing.expect(c.left == &a);
    try testing.expect(r.color == .black);
    try testing.expect(s.color == .black);
    try testing.expect(e.color == .red);
    try testing.expect(c.color == .black);
    try testing.expect(h.color == .black);
    try testing.expect(a.color == .red);
    try testing.expect(s.left == null);
    try testing.expect(s.right == null);
    try testing.expect(h.left == null);
    try testing.expect(h.right == null);
    try testing.expect(a.left == null);
    try testing.expect(a.right == null);
    try testing.expect(t.assertInvariants() == 1);
}

test "count/get/fetchPut" {
    //if (true) return error.SkipZigTest;
    var ttf = try TestTreeFactory.init(&[_]usize{ 26, 17, 41, 14, 21, 30, 47, 10, 16, 19, 23, 28, 38, 7, 12, 15, 20, 35, 39, 3 });
    const Node = TestTreeFactory.Tree.Node;
    defer ttf.deinit();
    var tree = ttf.tree;
    assert(tree.assertInvariants() == 3);
    try testing.expectEqual(@as(usize, 20), tree.count());

    try testing.expect(tree.get(7).?.key == 7);
    try testing.expect(tree.get(255) == null);
    var n7 = Node{ .key = 7, .data = {} };
    try testing.expect(tree.putNoClober(&n7) == Error.KeyExists);

    try tree.dot().save("tmp/rbt.dot");

    var replaced = tree.fetchPut(&n7);
    try testing.expect(replaced.?.key == 7);
    try testing.expect(replaced.? != &n7);
    try testing.expect(n7.left.?.key == 3);
    try testing.expect(n7.right == null);
    try testing.expect(n7.color == .black);

    // relaced pointers are deleted
    try testing.expect(replaced.?.left == null);
    try testing.expect(replaced.?.right == null);
    try testing.expect(replaced.?.color == .red);
}
