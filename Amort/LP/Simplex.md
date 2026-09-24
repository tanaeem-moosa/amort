# Simplex Slack Form and Dictionary Feasibility Invariants

> **Status: stub — not verified** (Phase 4 canon stub; ratio test feasibility is proven,
> but dictionary pivot loop and Bland termination are specification stubs).


This document details the Lean 4 formalization of Simplex Slack Form and Dictionary Invariants in `Amort.LP.Simplex`.

## Mathematical Architecture

### Dictionary Representation
A linear program in slack form partitions the variables into basic indices $B$ and non-basic indices $N$:
$$x_i = \bar{b}_i - \sum_{j \in N} \bar{a}_{ij} x_j \quad (i \in B)$$
$$z = v + \sum_{j \in N} \bar{c}_j x_j$$

The canonical basic solution sets all non-basic variables $x_j = 0$ for $j \in N$, yielding $x_i = \bar{b}_i$ for $i \in B$ and objective value $z = v$.

### Invariant Preservation Under Pivoting
Let $e \in N$ be the entering variable with $\bar{c}_e > 0$.
The maximum increase $\theta$ of $x_e$ without violating non-negativity of basic variables is bounded by the minimum ratio test:
$$\theta \le \frac{\bar{b}_i}{\bar{a}_{ie}} \quad \text{for all } i \in B \text{ with } \bar{a}_{ie} > 0$$

Under this bound, every basic variable value $x_i' = \bar{b}_i - \bar{a}_{ie} \theta$ remains non-negative:
1. If $\bar{a}_{ie} > 0$: $\bar{a}_{ie} \theta \le \bar{a}_{ie} (\bar{b}_i / \bar{a}_{ie}) = \bar{b}_i$, hence $x_i' \ge 0$.
2. If $\bar{a}_{ie} \le 0$: $-\bar{a}_{ie} \theta \ge 0$, hence $x_i' = \bar{b}_i - \bar{a}_{ie} \theta \ge \bar{b}_i \ge 0$.

Furthermore, the new dictionary constants $\bar{b}'$ after the pivot operation remain non-negative:
- Leaving row $l \in B$ becomes non-basic and $e$ becomes basic:
  $$\bar{b}'_e = \frac{\bar{b}_l}{\bar{a}_{le}} \ge 0$$
- Other basic rows $i \in B \setminus \{l\}$:
  $$\bar{b}'_i = \bar{b}_i - \bar{a}_{ie} \frac{\bar{b}_l}{\bar{a}_{le}} \ge 0$$

### Operational Complexity
Each simplex pivot step updates $m \times n$ coefficients, $m$ right-hand side constants, and $n$ cost coefficients:
$$\text{simplexPivotWork}(m, n) = m \cdot n + m + n \le (m + 1)(n + 1)$$
yielding $O(m \cdot n)$ work per pivot step.
