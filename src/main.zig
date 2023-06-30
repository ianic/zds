const std = @import("std");
const testing = std.testing;

const bst = @import("binary_search_tree.zig");
pub const BinarySearchTree = bst.BinarySearchTree;
pub const Error = bst.Error;
pub const compare = bst.compare;

pub const RedBlackTree = @import("red_black_tree.zig").RedBlackTree;
pub const RedBlackTreeRecursive = @import("red_black_tree_recursive.zig").RedBlackTree;

pub const PairingHeap = @import("pairing_heap.zig").PairingHeap;

test "basic add functionality" {
    _ = @import("binary_search_tree.zig");
    _ = @import("red_black_tree.zig");
    _ = @import("pairing_heap.zig");
    _ = @import("red_black_tree_recursive.zig");
}
