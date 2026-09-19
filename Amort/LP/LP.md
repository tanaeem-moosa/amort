# Linear Programming & Duality (`Amort.LP`)

This directory formalizes the foundational theory of Linear Programming (LP) and Duality in Lean 4:
1. **Primal and Dual Formulations**:
   - Primal linear program in standard inequality form: maximize $c^T x$ subject to $A x \le b$, $x \ge 0$.
   - Dual linear program: minimize $b^T y$ subject to $A^T y \ge c$, $y \ge 0$.
   - Feasibility predicates `PrimalFeasible` and `DualFeasible`.
2. **Weak Duality Theorem**:
   - For every primal feasible $x$ and dual feasible $y$:
     $$c^T x \le (A^T y)^T x = y^T (A x) \le y^T b = b^T y$$
3. **Optimality Certificate Theorem**:
   - If feasible solutions $x^*$ and $y^*$ satisfy $c^T x^* = b^T y^*$, then $x^*$ is globally optimal for
     the primal and $y^*$ is globally optimal for the dual.
   - Corollary: Unboundedness of primal implies infeasibility of dual; unboundedness of dual implies
     infeasibility of primal.
4. **Simplex Slack Form & Dictionary Invariant Preservation**:
   - Partition of variables into basic index set $B$ and non-basic index set $N$.
   - Dictionary equations $x_B = \bar{b} - \bar{A} x_N$, $z = v + \bar{c}^T x_N$.
   - Basic dictionary solution $(x_B, x_N) = (\bar{b}, 0)$ satisfies feasibility if and only if
     $\bar{b} \ge 0$.
   - Ratio test bound $\theta \le \bar{b}_i / \bar{a}_{ie}$ for $\bar{a}_{ie} > 0$.
   - Invariant preservation theorem: pivoting preserves non-negativity of basic solutions and
     dictionary constant vectors.
   - Objective strictly increases when $\bar{c}_e > 0$ and $\theta > 0$.
5. **Asymptotic Complexity Bridges**:
   - Operational step count for pivot step ($O(m \cdot n)$) and feasibility checking ($O(m \cdot n)$)
     connected to Mathlib's `Mathlib.Analysis.Asymptotics.IsBigO` under `Filter.atTop`.

## Module Map
- `Amort.LP.Duality`: `Amort/LP/Duality.lean`
- `Amort.LP.Simplex`: `Amort/LP/Simplex.lean`
- `Amort.LP.Asymptotics`: `Amort/LP/Asymptotics.lean`
