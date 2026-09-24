# Closest Pair of Points: Divide-and-Conquer & Strip Sparsity

> **Status: stub — not verified** (Phase 4 canon stub; geometric strip sparsity is proven,
> but divide-and-conquer execution algorithm is a specification stub).


## Geometric Packing Lemma
In any $\delta \times \delta$ square:
- Subdivide into 4 quadrants of size $(\delta / 2) \times (\delta / 2)$.
- The maximum distance between two points in the same quadrant is
  $\sqrt{2 (\delta/2)^2} = \delta / \sqrt{2} < \delta$.
- If all pairs of points have distance $\ge \delta$, no quadrant can contain more than 1 point.
- By the Pigeonhole Principle on 4 quadrants, the square contains at most 4 points.

## Strip Sparsity
- The $2\delta$-wide vertical strip around the dividing line is covered by 2 squares of size
  $\delta \times \delta$ (left and right).
- Each square contains at most 4 points, giving at most 8 points total in $[y_0, y_0 + \delta]$.
- Excluding the point itself, each point needs to be compared against at most 7 neighbors.
- Linear combine phase: $\le 7n$ comparisons.
- Recurrence $T(n) \le 2T(n/2) + c \cdot n \implies O(n \log n)$.
