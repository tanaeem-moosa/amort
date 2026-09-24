# Tarjan's Inverse Ackermann Bound for Disjoint Set Union (`Amort.Graph.Ackermann`)

> **Status: stub — not verified** (Phase 4 canon stubs; Tarjan Ackermann potential bound is
> a specification stub awaiting full verification).


This directory formalizes Tarjan's classical $O(m \cdot \alpha(n))$ amortized time bound for Disjoint
Set Union (DSU) with path compression and union-by-rank in Lean 4:

1. **Ackermann Hierarchy & Functional Inverse**:
   - The two-variable Ackermann function $A_k(n)$ with lexicographic well-founded termination.
   - Exact values: $A(0, 1) = 2, A(1, 1) = 3, A(2, 1) = 5, A(3, 1) = 13, A(4, 1) = 65533$.
   - Strict right-monotonicity: $A(k, n) < A(k, n + 1)$.
   - Functional inverse Ackermann function $\alpha(n) = \min \{ k \mid A(k, 1) \ge n \}$.
   - Extremal slow growth: $\alpha(n) \le 4$ for all practical integers $n \le 65533$.

2. **Path Compression with Union-by-Rank**:
   - Strict rank hierarchy: along parent pointers, $\text{rank}(v) < \text{rank}(\text{parent}(v))$.
   - Path compression flattens pointers to root $r$: $\text{parent}(u) := r$.
   - Preserves strict rank hierarchy and exponential subtree size invariant $2^{\text{rank}(v)} \le n$.
   - Logarithmic rank bound: $\text{rank}(v) \le \log_2 n \le \text{Nat.size } n$.

3. **Potential Function Analysis & Amortized Bound**:
   - Rank level intervals $[A_k(r), A_{k+1}(r)]$.
   - Potential assignment charging level changes and path compression decrements.
   - Telescoping amortized summation theorem bounding total work across $m$ operations on $n$ elements.
   - Operational work model $\text{dsuAckermannWork}(m, n) \le 6(m + n)(\alpha(n) + 1)$.

4. **Strict Asymptotic Complexity Bridges (`IsBigO` and `IsTheta`)**:
   - Matching lower bound: $((m + n)(\alpha(n) + 1)) = O(\text{dsuAckermannWork}(m, n))$.
   - Strict two-sided asymptotic tight bound:
     $$\text{dsuAckermannWork}(m, n) = \Theta((m + n)(\alpha(n) + 1)) \quad \text{under } \text{Filter.atTop}$$
   - Strict diagonal tight bound:
     $$\text{dsuAckermannDiag}(n) = \Theta(n \cdot (\alpha(n) + 1))$$
   - Non-constancy and level attainment: $\alpha(n)$ attains values $0, 1, 2, 3, 4, 5$ across the input range.

## Module Map
- `Amort.Graph.Ackermann.AckermannHierarchy`: `Amort/Graph/Ackermann/AckermannHierarchy.lean`
- `Amort.Graph.Ackermann.PathCompression`: `Amort/Graph/Ackermann/PathCompression.lean`
- `Amort.Graph.Ackermann.PotentialBound`: `Amort/Graph/Ackermann/PotentialBound.lean`
- `Amort.Graph.Ackermann.Asymptotics`: `Amort/Graph/Ackermann/Asymptotics.lean`
