# Computational Geometry Architecture (`Amort.Geometry`)

This suite formalizes foundational algorithms in 2D computational geometry:

1. **2D Convex Hull: Andrew's Monotone Chain** (`Amort/Geometry/ConvexHull.lean`):
   - **Point Representation**: Integer 2D coordinates `Point2D`.
   - **Orientation Determinant**: Cross product `cross(p, q, r)` testing left vs right turns.
   - **Monotone Chain Hull Construction**: Stack-based lower and upper hull computation.
   - **Amortized Analysis**: Potential function $\Phi = \text{stack.length}$ bounds the scanning
     phase to at most 2 operations per point ($\le 2n$ total operations).
   - **Overall Complexity**: $O(n \log n)$ dominated by coordinate sorting.

2. **Closest Pair of Points** (`Amort/Geometry/ClosestPair.lean`):
   - **Metric**: Squared Euclidean distance between integer points.
   - **Divide-and-Conquer**: Balanced median-$x$ split with $\delta = \min(\delta_L, \delta_R)$.
   - **Geometric Strip Sparsity / Packing Lemma**: Quadrant subdivision of a $\delta \times \delta$
     box proves that no box can contain more than 4 points with pairwise distance $\ge \delta$.
     Across the $2\delta$-wide vertical boundary strip, any point needs to be compared against
     at most 7 neighbors.
   - **Divide-and-Conquer Recurrence**: $T(n) \le 2T(n/2) + c \cdot n \implies O(n \log n)$.

3. **Asymptotics** (`Amort/Geometry/Asymptotics.lean`):
   - Mathlib `IsBigO` bridges for Convex Hull ($O(n \log n)$) and Closest Pair ($O(n \log n)$).
