const std = @import("std");
const mem = std.mem;
const log = std.log;
const zds = @import("zds");
const Instant = std.time.Instant;
const assert = std.debug.assert;
const print = std.debug.print;

fn compareStrings(_: void, lhs: []const u8, rhs: []const u8) std.math.Order {
    return mem.order(u8, lhs, rhs);
}

// Compare performance on loading dictionary and then checking whether a word is in the dictionary.
// Example of results:
//   123.334 ms load
//   string hash map
//   	16.597 ms total
//   	6.182 ms init
//   	10.415 ms get
//   	bytes used 13369424, per node: 56
//   red black tree
//   	99.753 ms total
//   	25.438 ms init
//   	74.314 ms get
//   	bytes used 16915436, per node: 72
//   binary search tree
//   	150.948 ms total
//   	63.059 ms init
//   	87.890 ms get
//      bytes used 14096204, per node: 60
//
// Run from project root:
// $ zig build -Doptimize=ReleaseSafe && zig-out/bin/spell_checker
// To download test files run from project root:
// $ mkdir -p tmp && cd tmp && wget https://introcs.cs.princeton.edu/java/data/war+peace.txt && wget https://introcs.cs.princeton.edu/java/data/web2.txt && cd ..
pub fn main() !void {
    const GPA = std.heap.GeneralPurposeAllocator(.{});
    var gpa: GPA = .{};
    defer _ = gpa.deinit();
    const alloc = gpa.allocator();

    const dictionary = "./tmp/web2.txt";
    const text_file = "./tmp/war+peace.txt";

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
    print("{d:.3} ms load\n", .{@as(f64, @floatFromInt(after_load.since(before_load))) / 1e6});

    var arena = std.heap.ArenaAllocator.init(alloc);
    defer arena.deinit();

    print("string hash map\n", .{});
    try hash(arena.allocator(), dict_words, words);
    print("\tbytes used {d}, per node: {d}\n", .{ arena.queryCapacity(), arena.queryCapacity() / dict_words.items.len });
    assert(arena.reset(.free_all));

    print("red black tree\n", .{});
    try rbt(arena.allocator(), dict_words, words);
    print("\tbytes used {d}, per node: {d}\n", .{ arena.queryCapacity(), arena.queryCapacity() / dict_words.items.len });
    assert(arena.reset(.free_all));

    print("binary search tree\n", .{});
    try bst(arena.allocator(), dict_words, words);
    print("\tbytes used {d}, per node: {d}\n", .{ arena.queryCapacity(), arena.queryCapacity() / dict_words.items.len });
    assert(arena.reset(.free_all));

    print("red black tree recursive\n", .{});
    try rbtr(arena.allocator(), dict_words, words);
    print("\tbytes used {d}, per node: {d}\n", .{ arena.queryCapacity(), arena.queryCapacity() / dict_words.items.len });
    assert(arena.reset(.free_all));
}

const WordsList = std.ArrayList([]u8);

fn hash(alloc: mem.Allocator, dict_words: WordsList, words: WordsList) !void {
    const before_fill = try Instant.now();

    var dict = std.StringHashMap(void).init(alloc);
    defer dict.deinit();

    try dict.ensureTotalCapacity(@intCast(dict_words.items.len));
    for (dict_words.items) |word| {
        try dict.putNoClobber(word, {});
    }

    const before_get = try Instant.now();
    var hits: usize = 0;
    var misses: usize = 0;
    for (words.items) |word| {
        dict.get(word) orelse {
            misses += 1;
            continue;
        };
        hits += 1;
    }
    const after_all = try Instant.now();

    assert(hits == 480250);
    assert(misses == 91994);

    print("\t{d:.3} ms total\n", .{@as(f64, @floatFromInt(after_all.since(before_fill))) / 1e6});
    print("\t{d:.3} ms init\n", .{@as(f64, @floatFromInt(before_get.since(before_fill))) / 1e6});
    print("\t{d:.3} ms get\n", .{@as(f64, @floatFromInt(after_all.since(before_get))) / 1e6});
}

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

    print("\t{d:.3} ms total\n", .{@as(f64, @floatFromInt(after_all.since(before_fill))) / 1e6});
    print("\t{d:.3} ms init\n", .{@as(f64, @floatFromInt(before_get.since(before_fill))) / 1e6});
    print("\t{d:.3} ms get\n", .{@as(f64, @floatFromInt(after_all.since(before_get))) / 1e6});
}

fn rbtr(alloc: mem.Allocator, dict_words: WordsList, words: WordsList) !void {
    const Tree = zds.RedBlackTreeRecursive([]const u8, void, void, compareStrings);
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

    print("\t{d:.3} ms total\n", .{@as(f64, @floatFromInt(after_all.since(before_fill))) / 1e6});
    print("\t{d:.3} ms init\n", .{@as(f64, @floatFromInt(before_get.since(before_fill))) / 1e6});
    print("\t{d:.3} ms get\n", .{@as(f64, @floatFromInt(after_all.since(before_get))) / 1e6});
}

fn bst(alloc: mem.Allocator, dict_words: WordsList, words: WordsList) !void {
    const Tree = zds.BinarySearchTree([]const u8, void, void, compareStrings);
    const Node = Tree.Node;

    const before_fill = try Instant.now();
    // fill dictionary
    var dp = std.rand.DefaultPrng.init(0); // dict_words are sorted without randomization we hit bst worst case
    dp.random().shuffle([]const u8, dict_words.items);

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

    print("\t{d:.3} ms total\n", .{@as(f64, @floatFromInt(after_all.since(before_fill))) / 1e6});
    print("\t{d:.3} ms init\n", .{@as(f64, @floatFromInt(before_get.since(before_fill))) / 1e6});
    print("\t{d:.3} ms get\n", .{@as(f64, @floatFromInt(after_all.since(before_get))) / 1e6});
}

fn readWords(alloc: mem.Allocator, file_name: []const u8) !WordsList {
    var words = WordsList.init(alloc);

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
