### Some notable data structures from Zig Standard Library

General purpose hash with preserved insertion order:
[array hash map](https://github.com/ziglang/zig/blob/master/lib/std/array_hash_map.zig)  

A contiguous, growable list of items in memory.
[array list](https://github.com/ziglang/zig/blob/master/lib/std/array_list.zig)  

<!--
A structure with an array and a length, that can be used as a slice.
[bounded array](https://github.com/ziglang/zig/blob/master/lib/std/bounded_array.zig)  
-->

[fifo](https://github.com/ziglang/zig/blob/master/lib/std/fifo.zig)  

Hash map (disctionary): 
[hash map](https://github.com/ziglang/zig/blob/master/lib/std/hash_map.zig)  

Data oriented struct store, array for each struct filed: 
[multi array list](https://github.com/ziglang/zig/blob/master/lib/std/multi_array_list.zig)

[priority queue](https://github.com/ziglang/zig/blob/master/lib/std/priority_queue.zig)

[priority dequeue](https://github.com/ziglang/zig/blob/master/lib/std/priority_dequeue.zig)

[segmented list](https://github.com/ziglang/zig/blob/master/lib/std/segmented_list.zig)

[singly linked list](https://github.com/ziglang/zig/blob/master/lib/std/linked_list.zig)  

[tail queue](https://github.com/ziglang/zig/blob/6f766fbf008160150a6a164c2dae5a6ee2a5543c/lib/std/linked_list.zig#L160)  

[treap](https://github.com/ziglang/zig/blob/master/lib/std/treap.zig)

### Pairing Heap

Implementation taken from [mitchellh/libxev](https://github.com/mitchellh/libxev/blob/main/src/heap.zig).  
Paper [The Pairing Heap: A New Form of Self-Adjusting Heap](https://www.cs.cmu.edu/~sleator/papers/pairing-heaps.pdf)
