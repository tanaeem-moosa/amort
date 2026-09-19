# Greedy Algorithms & Linear Selection Architecture (`Amort.Greedy`)

This suite formalizes classical greedy choice principles and deterministic linear selection in Lean 4:

1. **Interval Scheduling / Activity Selection** (`Amort/Greedy/IntervalScheduling.lean`):
   - **Compatible Intervals**: Modeled as structures with strictly positive duration $start < finish$.
   - **Greedy Earliest-Finish-Time Rule**: Selecting the compatible interval that finishes earliest.
   - **Exchange Argument Optimality**: Any arbitrary valid schedule can be transformed without
     reducing cardinality into one that begins with the greedy choice. By induction, the greedy
     schedule achieves global cardinality maximality.
   - **Operational Complexity**: $O(n \log n)$ dominated by coordinate sorting.

2. **Huffman Coding & Optimal Prefix Trees** (`Amort/Greedy/Huffman.lean`):
   - **Prefix Trees**: Inductive binary trees with weighted symbols at leaves.
   - **Weighted External Path Length**: $\sum w_i \cdot \text{depth}(i)$, proven strictly equivalent
     to the sum of all internal node weights via depth-shift recurrence.
   - **Greedy Choice Property**: Swapping the two lowest-frequency symbols with the two deepest
     sibling leaves preserves or decreases the weighted path length.
   - **Priority Queue Construction**: Bounded by $O(n \log n)$ via binary min-heap operations.

3. **Median-of-Medians Deterministic Selection (BFPRT)** (`Amort/Greedy/MedianOfMedians.lean`):
   - **Block Partitioning**: Partitioning into groups of 5 with median of medians pivot $x$.
   - **Pivot Quality Theorem**: At least $3 \lceil \lceil n/5 \rceil / 2 \rceil \ge 3n/10 - 6$
     elements are $\le x$ and $\ge x$, guaranteeing neither recursive partition branch exceeds
     $7n/10 + 6$ elements.
   - **Divide-and-Conquer Recurrence**: $T(n) \le T(\lceil n/5 \rceil) + T(7n/10 + 6) + c \cdot n$.
     Because $1/5 + 7/10 = 9/10 < 1$, strong induction establishes the linear bound
     $T(n) \le C \cdot n \implies O(n)$.

4. **Asymptotics** (`Amort/Greedy/Asymptotics.lean`):
   - Bridges connecting Interval Scheduling ($O(n \log n)$), Huffman Coding ($O(n \log n)$),
     and Median-of-Medians ($O(n)$) to Mathlib's `Mathlib.Analysis.Asymptotics.IsBigO` under
     `Filter.atTop`.
