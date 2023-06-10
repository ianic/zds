const std = @import("std");
const assert = std.debug.assert;

/// An intrusive heap implementation backed by a pairing heap[1] implementation.
///
/// Why? Intrusive data structures require the element type to hold the metadata
/// required for the structure, rather than an additional container structure.
/// There are numerous pros/cons that are documented well by Boost[2]. For Zig,
/// I think the primary benefits are making data structures allocation free
/// (rather, shifting allocation up to the consumer which can choose how they
/// want the memory to be available). There are various costs to this such as
/// the costs of pointer chasing, larger memory overhead, requiring the element
/// type to be aware of its container, etc. But for certain use cases an intrusive
/// data structure can yield much better performance.
///
/// Usage notes:
/// - The element T is expected to have a field "heap" of type InstrusiveHeapField.
///   See the tests for a full example of how to set this.
/// - You can easily make this a min or max heap by inverting the result of
///   "less" below.
///
/// [1]: https://en.wikipedia.org/wiki/Pairing_heap
/// [2]: https://www.boost.org/doc/libs/1_64_0/doc/html/intrusive/intrusive_vs_nontrusive.html
pub fn PairingHeap(
    comptime T: type,
    comptime Context: type,
    comptime less: *const fn (ctx: Context, a: *T, b: *T) bool,
) type {
    return struct {
        const Self = @This();

        root: ?*T = null,
        context: Context,

        /// Insert a new element v into the heap. An element v can only
        /// be a member of a single heap at any given time. When compiled
        /// with runtime-safety, assertions will help verify this property.
        pub fn insert(self: *Self, v: *T) void {
            self.root = if (self.root) |root| self.meld(v, root) else v;
            assert(self.root.?.heap.prev == null); // root doesn't have prev
            assert(self.root.?.heap.next == null); // root doesn't have siblings
        }

        /// Look at the next minimum value but do not remove it.
        pub fn peek(self: *Self) ?*T {
            return self.root;
        }

        /// Delete the minimum value from the heap and return it.
        pub fn deleteMin(self: *Self) ?*T {
            const root = self.root orelse return null;
            self.root = if (root.heap.child) |child|
                self.combine_siblings(child)
            else
                null;

            // Clear pointers with runtime safety so we can verify on
            // insert that values aren't incorrectly being set multiple times.
            root.heap = .{};

            return root;
        }

        /// Remove the value v from the heap.
        pub fn remove(self: *Self, v: *T) void {
            // If v doesn't have a previous value, this must be the root
            // element. If it is NOT the root element, v can't be in this
            // heap and we trigger an assertion failure.
            if (v.heap.prev == null) {
                assert(self.root.? == v);
                _ = self.deleteMin();
                return;
            }

            // If we have children, then we need to merge them back in.
            const child = detach(v) orelse return;
            const x = self.combine_siblings(child);
            self.root = self.meld(x, self.root.?);
        }

        /// Detach "v" from the tree and clean up any links so it
        /// is as if this node never existed. The previous value
        /// must point to the proper next value and the pointers
        /// must all be cleaned up.
        inline fn detach(v: *T) ?*T {
            assert(v.heap.prev != null);
            const prev = v.heap.prev.?;

            if (v.heap.next) |next| next.heap.prev = prev;
            if (prev.heap.child == v)
                prev.heap.child = v.heap.next
            else
                prev.heap.next = v.heap.next;
            v.heap.prev = null;
            v.heap.next = null;

            const child = v.heap.child;
            v.heap.child = null;
            return child;
        }

        /// Meld (union) two heaps together. This isn't a generalized
        /// union. It assumes that a.heap.next is null so this is only
        /// meant in specific scenarios in the pairing heap where meld
        /// is expected.
        ///
        /// For example, when melding a new value "v" with an existing
        /// root "root", "v" must always be the first param.
        ///
        /// Preserves B.next into result.next.
        /// Preserves A.prev into result.prev.
        ///
        /// Assumes A.next and B.prev pointers are null.
        ///
        ///     ap          :
        ///     |           |
        ///     A--:        B--bn
        ///    /           /
        ///   ac          bc
        ///
        ///  A.value < B.value
        ///
        ///         ap
        ///         |
        ///         A--bn
        ///        /
        ///       B--ac
        ///      /
        ///     bc
        ///
        ///  A.value >= B.value
        ///
        ///         ap
        ///         |
        ///         B--bn
        ///        /
        ///       A--bc
        ///      /
        ///     ac
        ///
        fn meld(self: *Self, a: *T, b: *T) *T {
            assert(a.heap.next == null);
            assert(b.heap.prev == null);

            if (less(self.context, a, b)) {
                // a is new root
                // b is child of a
                // previous b next is now a next
                // previous a child is now b next

                moveNext(b, a); // b.next to a.next
                makeChild(b, a); // b to a.child
                return a;
            }

            b.heap.prev = a.heap.prev;
            // b is new root
            // a is child of b
            // previous b child is now a next
            makeChild(a, b); // a to b.child
            return b;
        }

        // move a next to b next
        inline fn moveNext(a: *T, b: *T) void {
            assert(b.heap.next == null);
            if (a.heap.next) |a_next| {
                assert(a_next.heap.prev == a);
                b.heap.next = a_next;
                a_next.heap.prev = b;
                a.heap.next = null;
            }
        }

        // make a child of b
        // previous b child is moved to a next
        inline fn makeChild(a: *T, b: *T) void {
            assert(a.heap.next == null);
            // b.child to a.next
            if (b.heap.child) |b_child| {
                assert(b_child.heap.prev == b);
                a.heap.next = b_child;
                b_child.heap.prev = a;
                // b.heap.child = null; // valid but redundant, changed in the next line
            }
            // a to b.child
            b.heap.child = a;
            a.heap.prev = b;
        }

        /// Combine the siblings of the leftmost value "left" into a single
        /// new rooted with the minimum value.
        fn combine_siblings(self: *Self, left: *T) *T {
            return self.mergePairsLeft(self.mergePairsRight(left));
        }

        /// Processes and melds siblings in pairs first-second, third-fourth, ...
        /// Every pair has prev pointer leading to previous melded pair root.
        /// Returns right most sibling (odd) or rightmost melded pair (even
        /// number of siblings).
        ///
        /// Example of pairing after root(1) deletion.
        /// Root child is 3, 3's first sibling is 4...
        ///
        ///    1
        ///   /
        ///  3--6--4--2--10--8--5
        ///
        ///    3<-2<-8<-5
        ///   /  /  /
        ///  6  4  10
        ///
        /// Returns pointer to 5, 5 has prev to 8, 8 to 2, 2 to 3, 3 to null.
        /// There is no corresponding next pointers for this prevs.
        ///
        inline fn mergePairsRight(self: *Self, left: *T) *T {
            left.heap.prev = null;
            var a: *T = left;
            while (true) {
                var b = a.heap.next orelse return a;
                a.heap.next = null;
                b.heap.prev = null;
                b = self.meld(a, b); // b next is preseved into b
                a = b.heap.next orelse return b;
                b.heap.next = null;
            }
        }

        /// Uses heaps from the previous function follows prev pointers from
        /// rightmost and melds into single heap.
        ///
        ///    3<-2<-8<-5
        ///   /  /  /
        ///  6  4  10
        ///
        ///          2
        ///         /
        ///        3--5--4
        ///       /  /
        ///      6  8
        ///        /
        ///       10
        ///
        inline fn mergePairsLeft(self: *Self, right_: *T) *T {
            var right = right_; // make it mutable
            while (true) {
                var b = right.heap.prev orelse return right;
                right.heap.prev = null;
                assert(b.heap.next == null); // cleared in mergePairsRight
                right = self.meld(b, right); // b prev is preserved into right prev
            }
        }
    };
}

/// The state that is required for IntrusiveHeap element types. This
/// should be set as the "heap" field in the type T.
pub fn Field(comptime T: type) type {
    return struct {
        child: ?*T = null, // child values are not less then the parent value; half-ordered binary tree
        prev: ?*T = null, // points to parent or previous sibling
        next: ?*T = null, // next sibling
    };
}

const testing = std.testing;

// structure used in tests
const Elem = struct {
    const Self = @This();
    value: usize = 0,
    heap: Field(Self) = .{},
    fn less(ctx: void, a: *Self, b: *Self) bool {
        _ = ctx;
        return a.value < b.value;
    }
};

test "heap basic operations" {
    const Heap = PairingHeap(Elem, void, Elem.less);

    var a: Elem = .{ .value = 12 };
    var b: Elem = .{ .value = 24 };
    var c: Elem = .{ .value = 7 };
    var d: Elem = .{ .value = 9 };

    var h: Heap = .{ .context = {} };
    h.insert(&a);
    h.insert(&b);
    h.insert(&c);
    h.insert(&d);
    h.remove(&d);

    try testing.expect(h.deleteMin().?.value == 7);
    try testing.expect(h.deleteMin().?.value == 12);
    try testing.expect(h.deleteMin().?.value == 24);
    try testing.expect(h.deleteMin() == null);
}

test "heap remove root" {
    const Heap = PairingHeap(Elem, void, Elem.less);

    var a: Elem = .{ .value = 12 };
    var b: Elem = .{ .value = 24 };

    var h: Heap = .{ .context = {} };
    h.insert(&a);
    h.insert(&b);
    h.remove(&a);

    try testing.expect(h.deleteMin().?.value == 24);
    try testing.expect(h.deleteMin() == null);
}

test "heap remove with children" {
    const Heap = PairingHeap(Elem, void, Elem.less);

    var a: Elem = .{ .value = 36 };
    var b: Elem = .{ .value = 24 };
    var c: Elem = .{ .value = 12 };

    var h: Heap = .{ .context = {} };
    h.insert(&a);
    h.insert(&b);
    h.insert(&c);
    h.remove(&b);

    try testing.expect(h.deleteMin().?.value == 12);
    try testing.expect(h.deleteMin().?.value == 36);
    try testing.expect(h.deleteMin() == null);
}

test "heap equal values" {
    const Heap = PairingHeap(Elem, void, Elem.less);

    var a: Elem = .{ .value = 1 };
    var b: Elem = .{ .value = 2 };
    var c: Elem = .{ .value = 3 };
    var d: Elem = .{ .value = 4 };

    var h: Heap = .{ .context = {} };
    h.insert(&a);
    h.insert(&b);
    h.insert(&c);
    h.insert(&d);

    try testing.expect(h.deleteMin().?.value == 1);
    try testing.expect(h.deleteMin().?.value == 2);
    try testing.expect(h.deleteMin().?.value == 3);
    try testing.expect(h.deleteMin().?.value == 4);
    try testing.expect(h.deleteMin() == null);
}

test "heap: random values" {
    const alloc = testing.allocator;
    const RndGen = std.rand.DefaultPrng;
    var rnd = RndGen.init(0);

    const num_runs = 1024;
    var runs: usize = 0;
    while (runs < num_runs) : (runs += 1) {
        const Heap = PairingHeap(Elem, void, Elem.less);

        const num_elems: usize = 1024;
        var elems = try alloc.alloc(Elem, num_elems);
        defer alloc.free(elems);

        var i: usize = 0;
        var value: usize = 0;
        while (i < num_elems) : (i += 1) {
            value = rnd.random().int(u32);
            elems[i] = .{ .value = value };
        }

        var h: Heap = .{ .context = {} };
        for (elems) |*elem| {
            h.insert(elem);
        }

        var count: usize = 0;
        var last: usize = 0;
        while (h.deleteMin()) |elem| {
            count += 1;
            try testing.expect(elem.value >= last);
            last = elem.value;
        }
        try testing.expect(h.deleteMin() == null);
        try testing.expect(count == num_elems);
    }
}

test "heap: remove random values" {
    const alloc = testing.allocator;
    const RndGen = std.rand.DefaultPrng;
    var rnd = RndGen.init(0);

    const num_runs = 1024;
    var runs: usize = 0;
    while (runs < num_runs) : (runs += 1) {
        const Heap = PairingHeap(Elem, void, Elem.less);

        const num_elems: usize = 1024;
        var elems = try alloc.alloc(Elem, num_elems);
        defer alloc.free(elems);

        var i: usize = 0;
        var value: usize = 0;
        while (i < num_elems) : (i += 1) {
            value = rnd.random().int(u32);
            elems[i] = .{ .value = value };
        }

        var h: Heap = .{ .context = {} };
        for (elems) |*elem| {
            h.insert(elem);
        }

        for (elems) |*elem| {
            h.remove(elem);
        }
        try testing.expect(h.deleteMin() == null);
    }
}

test "heap: this was failing in intial implementation" {
    const Heap = PairingHeap(Elem, void, Elem.less);

    var a: Elem = .{ .value = 2 };
    var b: Elem = .{ .value = 4 };
    var c: Elem = .{ .value = 5 };
    var d: Elem = .{ .value = 1 };
    var e: Elem = .{ .value = 3 };

    var h: Heap = .{ .context = {} };
    h.insert(&a);
    h.insert(&b);
    h.insert(&c);
    h.insert(&d);
    h.insert(&e);

    try testing.expect(h.deleteMin().?.value == 1);
    try testing.expect(h.deleteMin().?.value == 2);
    try testing.expect(h.deleteMin().?.value == 3);
    try testing.expect(h.deleteMin().?.value == 4);
    try testing.expect(h.deleteMin().?.value == 5);
    try testing.expect(h.deleteMin() == null);
}

test "heap: combine siblings" {
    const num_elems = 32;
    var elems: [num_elems]Elem = undefined;
    for (&elems, 0..) |*elem, i| {
        elem.* = .{ .value = i };
    }

    const Heap = PairingHeap(Elem, void, Elem.less);
    var h: Heap = .{ .context = {} };

    var root = elems[0];
    h.insert(&root);

    var a: *Elem = h.root.?;
    var n: usize = num_elems - 1;
    while (n > 0) : (n -= 1) {
        var b = &elems[n];
        a.heap.next = b;
        b.heap.prev = a;
        a = b;
    }

    a = h.root.?;
    a.heap.child = a.heap.next;
    a.heap.next = null;

    n = 0;
    while (n < num_elems) : (n += 1) {
        try testing.expect(h.deleteMin().?.value == n);
        //if (n == 0) printDotGraph(Elem, h.root.?);
    }
}

// Paper: https://www.cs.cmu.edu/~sleator/papers/pairing-heaps.pdf
test "heap: example from the paper (fig. 7)" {
    const Heap = PairingHeap(Elem, void, Elem.less);
    var h: Heap = .{ .context = {} };

    var e1: Elem = .{ .value = 1 };
    var e2: Elem = .{ .value = 2 };
    var e3: Elem = .{ .value = 3 };
    var e4: Elem = .{ .value = 4 };
    var e5: Elem = .{ .value = 5 };
    var e6: Elem = .{ .value = 6 };
    var e8: Elem = .{ .value = 8 };
    var e10: Elem = .{ .value = 10 };

    // zig fmt: off
    e1.heap.child = &e3;  e3.heap.prev  = &e1;
    e3.heap.next  = &e6;  e6.heap.prev  = &e3;
    e6.heap.next  = &e4;  e4.heap.prev  = &e6;
    e4.heap.next  = &e2;  e2.heap.prev  = &e4;
    e2.heap.next  = &e10; e10.heap.prev = &e2;
    e10.heap.next = &e8;  e8.heap.prev  = &e10;
    e8.heap.next  = &e5;  e5.heap.prev  = &e8;
    // zig fmt: on

    var right = h.mergePairsRight(&e3);
    try testing.expect(e3.heap.prev == null);
    // test intermediate structure after first step
    try testing.expect(right.value == 5);
    try testing.expect(right.heap.child == null);
    try testing.expect(right.heap.next == null);
    var prev = right.heap.prev.?;
    try testing.expect(prev.value == 8);
    try testing.expect(prev.heap.next == null);
    try testing.expect(prev.heap.child.?.value == 10);
    prev = prev.heap.prev.?;
    try testing.expect(prev.value == 2);
    try testing.expect(prev.heap.next == null);
    try testing.expect(prev.heap.child.?.value == 4);
    prev = prev.heap.prev.?;
    try testing.expect(prev.value == 3);
    try testing.expect(prev.heap.next == null);
    try testing.expect(prev.heap.child.?.value == 6);
    try testing.expect(prev.heap.prev == null);

    var root = h.mergePairsLeft(right);
    // test resulted structure after both steps
    try testing.expect(root.value == 2);
    try testing.expect(root.heap.child.?.value == 3);
    try testing.expect(root.heap.child.?.heap.child.?.value == 6);
    try testing.expect(root.heap.child.?.heap.next.?.value == 5);
    try testing.expect(root.heap.child.?.heap.next.?.heap.next.?.value == 4);
    try testing.expect(root.heap.child.?.heap.next.?.heap.child.?.value == 8);
    try testing.expect(root.heap.child.?.heap.next.?.heap.child.?.heap.child.?.value == 10);
}

fn printDotGraph(comptime T: type, root: *T) void {
    const print = std.debug.print;
    print("\ndigraph {{\n", .{});
    printPointers(T, root, null);
    print("}}\n", .{});
}

fn printPointers(comptime T: type, e: *T, prev: ?*T) void {
    const print = std.debug.print;
    if (prev) |p| {
        if (e.heap.prev != p) {
            print("\t{d} -> {d} [label=\"prev missing\"];\n", .{ e.value, p.value });
            print("\t{d} -> {d} [label=\"prev\"];\n", .{ e.value, e.heap.prev.?.value });
        }
    }
    if (e.heap.child) |c| {
        print("\t{d} -> {d} [label=\"child\"];\n", .{ e.value, c.value });
        printPointers(T, c, e);
    }
    if (e.heap.next) |n| {
        print("\t{d} -> {d} [label=\"next\"];\n", .{ e.value, n.value });
        printPointers(T, n, e);
    }
}
