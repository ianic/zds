const std = @import("std");
const mem = std.mem;
const log = std.log;
const zds = @import("zds");
const Instant = std.time.Instant;
const assert = std.debug.assert;
const print = std.debug.print;

const Heap = zds.pairing_heap.Heap(Timer, void, Timer.less);
const number_of_timers = 10_000_000;

const Timer = struct {
    const Self = @This();
    heap: zds.pairing_heap.Field(Self) = .{},

    expires: usize,

    fn less(_: void, self: *Timer, other: *Timer) bool {
        return self.expires < other.expires;
    }

    fn compare(_: void, self: *Timer, other: *Timer) std.math.Order {
        return std.math.order(self.expires, other.expires);
    }
};

// benchmark:
//   pairing heap
//           16016.835 ms total
//           0.005 ms alloc
//           157.034 ms init
//           15859.796 ms deleteMin
//           bytes used 480000044, per node: 48
//   std priority queue
//           7509.926 ms total
//           0.014 ms alloc
//           247.937 ms init
//           7261.975 ms deleteMin
//           bytes used 787087264, per node: 78
//
pub fn main() !void {
    const GPA = std.heap.GeneralPurposeAllocator(.{});
    var gpa: GPA = .{};
    defer _ = gpa.deinit();
    const alloc = gpa.allocator();

    var arena = std.heap.ArenaAllocator.init(alloc);
    defer arena.deinit();

    print("pairing heap\n", .{});
    try pairing_heap(arena.allocator());
    print("\tbytes used {d}, per node: {d}\n", .{ arena.queryCapacity(), arena.queryCapacity() / number_of_timers });
    assert(arena.reset(.free_all));

    print("std priority queue\n", .{});
    try std_priority_queue(arena.allocator());
    print("\tbytes used {d}, per node: {d}\n", .{ arena.queryCapacity(), arena.queryCapacity() / number_of_timers });
    assert(arena.reset(.free_all));
}

fn pairing_heap(alloc: mem.Allocator) !void {
    const before_alloc = try Instant.now();
    var timers = try alloc.alloc(Timer, number_of_timers);
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
    print("\t{d:.3} ms total\n", .{@as(f64, @floatFromInt(after_all.since(before_alloc))) / 1e6});
    print("\t{d:.3} ms alloc\n", .{@as(f64, @floatFromInt(before_init.since(before_alloc))) / 1e6});
    print("\t{d:.3} ms init\n", .{@as(f64, @floatFromInt(after_init.since(before_init))) / 1e6});
    print("\t{d:.3} ms deleteMin\n", .{@as(f64, @floatFromInt(after_all.since(after_init))) / 1e6});
}

fn std_priority_queue(alloc: mem.Allocator) !void {
    const Queue = std.PriorityQueue(*Timer, void, Timer.compare);
    var queue = Queue.init(alloc, {});
    defer queue.deinit();

    const before_alloc = try Instant.now();
    try queue.ensureTotalCapacity(number_of_timers);
    var timers = try alloc.alloc(Timer, number_of_timers);
    defer alloc.free(timers);

    var expire_times = try alloc.alloc(usize, timers.len);
    defer alloc.free(expire_times);

    const before_init = try Instant.now();
    for (expire_times, 0..) |*k, i| k.* = i;
    var prng = std.rand.DefaultPrng.init(0);
    prng.random().shuffle(usize, expire_times);

    for (expire_times, 0..) |e, i| {
        var timer = &timers[i];
        timer.* = .{
            .expires = e,
            .heap = .{},
        };
        try queue.add(timer);
    }
    const after_init = try Instant.now();

    var i: usize = 0;
    while (queue.removeOrNull()) |timer| {
        assert(timer.expires == i);
        i += 1;
    }

    const after_all = try Instant.now();
    print("\t{d:.3} ms total\n", .{@as(f64, @floatFromInt(after_all.since(before_alloc))) / 1e6});
    print("\t{d:.3} ms alloc\n", .{@as(f64, @floatFromInt(before_init.since(before_alloc))) / 1e6});
    print("\t{d:.3} ms init\n", .{@as(f64, @floatFromInt(after_init.since(before_init))) / 1e6});
    print("\t{d:.3} ms deleteMin\n", .{@as(f64, @floatFromInt(after_all.since(after_init))) / 1e6});
}
