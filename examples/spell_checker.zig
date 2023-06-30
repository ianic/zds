const std = @import("std");
const mem = std.mem;
const zds = @import("zds");
const Instant = std.time.Instant;
const assert = std.debug.assert;

fn compareStrings(_: void, lhs: []const u8, rhs: []const u8) std.math.Order {
    return mem.order(u8, lhs, rhs);
}
pub fn main() !void {
    const GPA = std.heap.GeneralPurposeAllocator(.{});
    var gpa: GPA = .{};
    defer _ = gpa.deinit();
    const alloc = gpa.allocator();

    const dictionary = "../tmp/web2.txt";
    const text_file = "../tmp/war+peace.txt";

    const before_load = try Instant.now();
    var dict_words = try readWords(alloc, dictionary);
    defer {
        for (dict_words.items) |word|
            alloc.free(word);
        dict_words.deinit();
    }

    var words = try readWords(alloc, text_file);
    defer {
        for (words.items) |word|
            alloc.free(word);
        words.deinit();
    }
    const after_load = try Instant.now();
    std.log.info("{d:.3} ms load", .{@as(f64, @floatFromInt(after_load.since(before_load))) / 1e6});

    try rbt(alloc, dict_words, words);
    //try bst(alloc, dict_words, words);
}

const WordsList = std.ArrayList([]u8);

fn rbt(alloc: mem.Allocator, dict_words: WordsList, words: WordsList) !void {
    const Tree = zds.RedBlackTree([]const u8, void, void, compareStrings);
    const Node = Tree.Node;

    const before_fill = try Instant.now();
    // fill dictionary
    var dict = Tree{ .context = {} };
    var dict_nodes = try alloc.alloc(Node, dict_words.items.len);
    defer alloc.free(dict_nodes);
    for (dict_words.items, 0..) |word, i| {
        var node = &dict_nodes[i];
        node.* = Node{
            .key = word,
            .data = {},
        };
        try dict.putNoClobber(node);
    }

    const before_get = try Instant.now();
    var hits: usize = 0;
    var misses: usize = 0;
    for (words.items) |word| {
        _ = dict.get(word) orelse {
            misses += 1;
            continue;
        };
        hits += 1;
    }
    const after_all = try Instant.now();

    assert(hits == 480250);
    assert(misses == 91994);
    //std.debug.print("hits: {d}, misses: {d}\n", .{ hits, misses });

    std.log.info("{d:.3} ms total", .{@as(f64, @floatFromInt(after_all.since(before_fill))) / 1e6});
    std.log.info("{d:.3} ms init", .{@as(f64, @floatFromInt(before_get.since(before_fill))) / 1e6});
    std.log.info("{d:.3} ms get", .{@as(f64, @floatFromInt(after_all.since(before_get))) / 1e6});
}

fn bst(alloc: mem.Allocator, dict_words: WordsList, words: WordsList) !void {
    const Tree = zds.BinarySearchTree([]const u8, void, void, compareStrings);
    const Node = Tree.Node;

    const before_fill = try Instant.now();
    // fill dictionary
    var dict = Tree{ .context = {} };
    var dict_nodes = try alloc.alloc(Node, dict_words.items.len);
    defer alloc.free(dict_nodes);
    for (dict_words.items, 0..) |word, i| {
        var node = &dict_nodes[i];
        node.* = Node{
            .key = word,
            .data = {},
        };
        try dict.putNoClobber(node);
    }

    const before_get = try Instant.now();
    var hits: usize = 0;
    var misses: usize = 0;
    for (words.items) |word| {
        _ = dict.get(word) orelse {
            misses += 1;
            continue;
        };
        hits += 1;
    }
    const after_all = try Instant.now();

    assert(hits == 480250);
    assert(misses == 91994);
    //std.debug.print("hits: {d}, misses: {d}\n", .{ hits, misses });

    std.log.info("{d:.3} ms total", .{@as(f64, @floatFromInt(after_all.since(before_fill))) / 1e6});
    std.log.info("{d:.3} ms init", .{@as(f64, @floatFromInt(before_get.since(before_fill))) / 1e6});
    std.log.info("{d:.3} ms get", .{@as(f64, @floatFromInt(after_all.since(before_get))) / 1e6});
}

fn readWords(alloc: mem.Allocator, file_name: []const u8) !std.ArrayList([]u8) {
    var words = std.ArrayList([]u8).init(alloc);

    var file = try std.fs.cwd().openFile(file_name, .{});
    defer file.close();

    var buf_reader = std.io.bufferedReader(file.reader());
    var in_stream = buf_reader.reader();

    var buf: [128]u8 = undefined;
    var i: usize = 0;
    var n: usize = 0;
    while (true) {
        var c = in_stream.readByte() catch |err| {
            if (err == error.EndOfStream) {
                break;
            }
            return err;
        };
        if (std.ascii.isAlphanumeric(c)) {
            buf[i] = c; //std.ascii.toLower(c);
            if (std.ascii.isDigit(c))
                n += 1;
            i += 1;
        } else {
            if (i > 0 and n != i) {
                var word = try alloc.alloc(u8, i);
                mem.copy(u8, word, buf[0..i]);
                try words.append(word);
            }
            i = 0;
            n = 0;
        }
    }
    return words;
}
