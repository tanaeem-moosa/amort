# Median-of-Medians Deterministic Selection (BFPRT)

> **Status: stub — not verified** (Phase 3 canon stub; BFPRT recurrence is proven,
> but linear selection algorithm execution is a specification stub).


## Algorithm Structure
1. Group $n$ elements into $\lceil n/5 \rceil$ blocks of size 5.
2. Find the median of each group in $O(1)$ comparisons per group.
3. Recursively find the median of medians $x$ among the $\lceil n/5 \rceil$ group medians.
4. Partition input elements around pivot $x$.
5. Recurse into the subproblem containing the rank $k$ element.

## Pivot Quality Theorem
- At least half of the group medians are $\ge x$, meaning at least $\lceil \lceil n/5 \rceil / 2 \rceil$ groups.
- In each such group, at least 3 elements are $\ge$ the group median, hence $\ge x$.
- Discounting boundary groups, the number of elements $\ge x$ (and $\le x$) is at least:
  $$3 (\lceil \lceil n/5 \rceil / 2 \rceil - 2) \ge \frac{3n}{10} - 6$$
- Consequently, neither partition subproblem can exceed:
  $$n - \left( \frac{3n}{10} - 6 \right) \le \frac{7n}{10} + 6$$

## Recurrence & Linear Time Bound
The worst-case recurrence is:
$$T(n) \le T(\lceil n/5 \rceil) + T(7n/10 + 6) + c \cdot n$$
Since $1/5 + 7/10 = 9/10 < 1$, for $n \ge 140$ we have $(n+4)/5 + (7n/10 + 6) \le 19n/20$.
Strong induction establishes $T(n) \le C \cdot n$ for all $n \ge 1$ with $C = \max(B, 30c)$,
yielding $O(n)$ linear time.
