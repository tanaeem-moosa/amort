# Interval Scheduling / Activity Selection

## Mathematical Specification
An interval $I = [start, finish)$ satisfies $start < finish$.
Two intervals $i_1, i_2$ are compatible if $i_1.finish \le i_2.start \lor i_2.finish \le i_1.start$.
A sequence of intervals is chain-compatible if each interval finishes before or at the start
of the subsequent interval.

## Exchange Argument Proof Strategy
Given an input list $L$ sorted by finish time:
1. Greedy choice $g$: the first interval in $L$ with $lastFinish \le g.start$.
2. Any competing valid schedule $S = [s_0, s_1, \dots, s_{k-1}]$ respecting $lastFinish$ has
   $lastFinish \le s_0.start$.
3. Since $g$ is the earliest-finish interval satisfying the start condition in the sorted list,
   $g.finish \le s_0.finish$.
4. Compatibility of $S$ implies $s_0.finish \le s_1.start$, so by transitivity $g.finish \le s_1.start$.
5. Replacing $s_0$ with $g$ yields a valid schedule $g :: [s_1, \dots, s_{k-1}]$ of the exact same
   cardinality starting with the greedy choice.
6. Induction on schedule length establishes that no valid schedule can exceed the size of the
   greedy schedule.

## Complexity Bounds
- Sorting by finish time: $n \cdot \text{Nat.size } n$ comparisons.
- Greedy linear scan: $n$ steps.
- Total work: $W(n) = n \cdot \text{Nat.size } n + n \le 2n \cdot \text{Nat.size } n = O(n \log n)$.
