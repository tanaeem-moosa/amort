# Textbook Dynamic Programming in Lean 4

> **Status: partially verified / contains stubs** (Contains verified Knapsack and LIS algorithms
> alongside Phase 3 Matrix Chain stubs).


This document synthesizes the formalization of classical dynamic programming algorithms in
`Amort.DP`, connecting the state-space complexity framework (`Amort.Recurrence.DP`) to
three fundamental algorithmic paradigms:
1. **Interval DP**: Matrix Chain Multiplication ($O(n^3)$).
2. **Grid DP**: 0/1 Knapsack Problem ($O(n \cdot W)$).
3. **Predecessor State-Space DP**: Longest Increasing Subsequence ($O(n^2)$).

All modules connect concrete step bounds to Mathlib's `Mathlib.Analysis.Asymptotics.IsBigO`
under `Filter.atTop`, with complete proofs relying exclusively on Lean 4 foundational axioms.

---

## 1. Architectural Overview

```
Amort/
├── Amort.lean                  -- Library root re-exporting all modules
├── Recurrence/
│   ├── DP.lean                 -- Abstract DPModel, GridDP, and IsBigO bridges
│   └── Composition.lean        -- Compositional complexity algebra (nested loops, sums)
└── DP/
    ├── MatrixChain.lean        -- Interval DP: Matrix Chain Multiplication (O(n^3))
    ├── Knapsack.lean           -- Grid DP: 0/1 Knapsack & subcollection optimality (O(n * W))
    ├── LIS.lean                -- Predecessor DP: Longest Increasing Subsequence (O(n^2))
    ├── Asymptotics.lean        -- Unified Mathlib IsBigO asymptotic theorems
    ├── MatrixChain.md          -- Interval DP documentation & proofs
    ├── Knapsack.md             -- Grid DP documentation & proofs
    ├── LIS.md                  -- LIS documentation & proofs
    └── DP.md                   -- Architecture synthesis and comparison
```

---

## 2. Comparison of Dynamic Programming Paradigms

| Algorithm | State Space $S$ | Card $|S|$ | Local Work $c(s)$ | Total Bound | Asymptotics |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **Matrix Chain** | $\text{IntervalState } n := \{ (i, j) \mid i \le j < n \}$ | $\frac{n(n+1)}{2} \le n^2$ | $j - i \le n$ split choices | $n^3$ | $O(n^3)$ |
| **0/1 Knapsack** | $\text{Fin}(n + 1) \times \text{Fin}(W + 1)$ | $(n + 1)(W + 1)$ | $1$ (unit transition) | $(n + 1)(W + 1)$ | $O(n \cdot W)$ |
| **LIS** | $\text{Fin } n$ | $n$ | $i$ predecessor checks | $\frac{n(n-1)}{2} \le n^2$ | $O(n^2)$ |

---

## 3. The `Amort.Recurrence.DP` Framework Connection

In textbook dynamic programming, algorithms evaluate subproblem states in a DAG:
- Each distinct state $s \in S$ is evaluated at most once (memoization / bottom-up table).
- At state $s$, the non-recursive operational work is $c(s) \le C$.
- The total operations across all states is $\sum_{s \in S} c(s) \le |S| \cdot C$.

### 3.1 Interval DP (`MatrixChain.lean`)
- Embeds into `DPModel (IntervalState n)` where $|IntervalState n| = n(n+1)/2 \le n^2$.
- Local work at interval $(i, j)$ tests split points $k \in [i, j)$, with $j - i \le n$.
- Total operations bounded by $|IntervalState n| \cdot n \le n^2 \cdot n = n^3$.

### 3.2 Grid DP (`Knapsack.lean`)
- Instantiates `GridDP n W` (specialized to $(n + 1) \times (W + 1)$ grid).
- Unit transition per cell ($C = 1$), directly yielding $(n + 1)(W + 1)$.
- Mathematical correctness proves the DP computes the exact maximum across all subsets
  $s \subseteq \{0, \dots, n-1\}$ with $\sum_{j \in s} w_j \le W$.

### 3.3 Predecessor State-Space DP (`LIS.lean`)
- Embeds into `DPModel (Fin n)` with $n$ states.
- Local work at state $i$ examines predecessors $j < i$, taking $i \le n$ comparisons.
- Total operations $\sum_{i=0}^{n-1} i = n(n-1)/2 \le n^2$.
- Mathematical correctness proves the DP computes the exact length of the longest
  strictly increasing sublist of $xs$.

---

## 4. Asymptotic Complexity in Mathlib `IsBigO`

All bounds are lifted to `Mathlib.Analysis.Asymptotics.IsBigO` under `Filter.atTop` in
`Amort.DP.Asymptotics`:
- `isBigO_matrixChainDP_totalCost_atTop`: Matrix Chain DP total cost is $O(n^3)$.
- `isBigO_knapsackGridDP_totalCost_atTop`: Knapsack Grid DP total cost is $O(n \cdot W)$.
- `isBigO_lisDP_totalCost_atTop`: LIS DP total cost is $O(n^2)$.

All proofs are foundational, clean, and verified with 0 `sorryAx`.
