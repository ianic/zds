const std = @import("std");
const mem = std.mem;

pub fn main() !void {
    const GPA = std.heap.GeneralPurposeAllocator(.{});
    var gpa: GPA = .{};
    defer _ = gpa.deinit();
    const alloc = gpa.allocator();

    const dictionary = "../tmp/web2.txt";
    const text_file = "../tmp/war+peace.txt";

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

    for (words.items) |word| {
        std.debug.print("{s} ", .{word});
    }
}

fn readFileLinse(alloc: mem.Allocator, file_name: []const u8) !std.ArrayList([]const u8) {
    var lines = std.ArrayList([]const u8).init(alloc);

    var file = try std.fs.cwd().openFile(file_name, .{});
    defer file.close();

    var buf_reader = std.io.bufferedReader(file.reader());
    var in_stream = buf_reader.reader();

    var buf: [128]u8 = undefined;
    while (try in_stream.readUntilDelimiterOrEof(&buf, '\n')) |line| {
        if (line.len == 0) continue;

        var line_buf = try alloc.alloc(u8, line.len);
        mem.copy(u8, line_buf, line);

        //std.debug.print("{d} {s}\n", .{ line_buf.len, line_buf });
        try lines.append(line_buf);
    }
    return lines;
}

fn readWords(alloc: mem.Allocator, file_name: []const u8) !std.ArrayList([]const u8) {
    var words = std.ArrayList([]const u8).init(alloc);

    var file = try std.fs.cwd().openFile(file_name, .{});
    defer file.close();

    var buf_reader = std.io.bufferedReader(file.reader());
    var in_stream = buf_reader.reader();

    var buf: [128]u8 = undefined;
    var i: usize = 0;
    while (true) {
        var c = in_stream.readByte() catch |err| {
            if (err == error.EndOfStream) {
                break;
            }
            return err;
        };
        if (std.ascii.isAlphanumeric(c)) {
            buf[i] = c;
            i += 1;
        } else {
            if (i > 0) {
                var word = try alloc.alloc(u8, i);
                mem.copy(u8, word, buf[0..i]);
                try words.append(word);
                i = 0;
            }
        }
    }
    return words;
}
