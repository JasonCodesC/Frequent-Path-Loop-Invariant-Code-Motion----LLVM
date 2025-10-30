# Frequent Path Loop Invariant Code Motion in LLVM


## How it works:

First, find the hot path starting at the loop header. We follow successors inside the loop whose edge probability >= 80%, stopping at a backedge to the header.

Then we partition the loop and so blocks on this path are frequent and the rest are infrequent.

We then collect all stores for both regions. A load is eligible to be hoisted if it has stores only in infrequent blocks and no stores on the frequent path.

In the loop preheader we then allocate a slot, initialize it by loading the original pointer once, and then replace hot-path loads of that pointer with loads from the slot.

After each infrequent store to the original pointer, we insert a repair load from memory and store the fresh value back to the slot, deduplicated per store.

## Motivations:
This project was completed for the graduate level compilers course at the University of Michigan. 
It's meant to serve as a project to get familar with basic optamizations and get stronger LLVM skills.
Following this I will be completing a far bigger project on superword level parallelism with vectorization.

## Authors
- Jason Majoros
