const std = @import("std");
const mem = std.mem;
const log = std.log;
const zds = @import("zds");
const Instant = std.time.Instant;
const assert = std.debug.assert;
const print = std.debug.print;

const Heap = zds.pairing_heap.Heap(Timer, void, Timer.less);

const Timer = struct {
    const Self = @This();
    heap: zds.pairing_heap.Field(Self) = .{},

    expires: usize,

    fn less(_: void, self: *Timer, other: *Timer) bool {
        return self.expires < other.expires;
    }
};

pub fn main() !void {
    const GPA = std.heap.GeneralPurposeAllocator(.{});
    var gpa: GPA = .{};
    defer _ = gpa.deinit();
    const alloc = gpa.allocator();

    const before_alloc = try Instant.now();
    var timers = try alloc.alloc(Timer, 10_000_000);
    defer alloc.free(timers);

    var expire_times = try alloc.alloc(usize, timers.len);
    defer alloc.free(expire_times);

    const before_init = try Instant.now();
    for (expire_times, 0..) |*k, i| k.* = i;
    var prng = std.rand.DefaultPrng.init(0);
    prng.random().shuffle(usize, expire_times);

    var heap: Heap = .{ .context = {} };
    for (expire_times, 0..) |e, i| {
        var timer = &timers[i];
        timer.* = .{
            .expires = e,
            .heap = .{},
        };
        heap.insert(timer);
    }
    const after_init = try Instant.now();

    var i: usize = 0;
    while (heap.deleteMin()) |timer| {
        assert(timer.expires == i);
        i += 1;
    }
    const after_all = try Instant.now();

    print("{d:.3} ms total\n", .{@as(f64, @floatFromInt(after_all.since(before_alloc))) / 1e6});
    print("{d:.3} ms alloc\n", .{@as(f64, @floatFromInt(before_init.since(before_alloc))) / 1e6});
    print("{d:.3} ms init\n", .{@as(f64, @floatFromInt(after_init.since(before_init))) / 1e6});
    print("{d:.3} ms deleteMin\n", .{@as(f64, @floatFromInt(after_all.since(after_init))) / 1e6});
}
