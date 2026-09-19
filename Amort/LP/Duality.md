# Linear Programming Duality: Weak Duality and Optimality Certificates

This document details the Lean 4 formalization of Linear Programming Duality in `Amort.LP.Duality`.

## Mathematical Formulations

### Standard Inequality Form
For matrix $A \in \mathbb{R}^{m \times n}$, right-hand side vector $b \in \mathbb{R}^m$, and cost vector $c \in \mathbb{R}^n$:
- **Primal Problem**:
  $$\max \quad c^T x \quad \text{s.t.} \quad A x \le b, \quad x \ge 0$$
- **Dual Problem**:
  $$\min \quad b^T y \quad \text{s.t.} \quad A^T y \ge c, \quad y \ge 0$$

### Weak Duality Theorem
For any primal feasible solution $x$ and dual feasible solution $y$:
$$c^T x = \sum_{j=1}^n c_j x_j \le \sum_{j=1}^n (A^T y)_j x_j = \sum_{j=1}^n \sum_{i=1}^m A_{ij} y_i x_j = \sum_{i=1}^m y_i (A x)_i \le \sum_{i=1}^m y_i b_i = b^T y$$

In Lean, this is verified formally using dot product monotonicity on non-negatives and the transpose adjoint identity:
```lean
theorem weak_duality (A : Matrix m n ℝ) (b : m → ℝ) (c : n → ℝ)
    {x : n → ℝ} {y : m → ℝ}
    (hx : PrimalFeasible A b x) (hy : DualFeasible A c y) :
    c ⬝ᵥ x ≤ b ⬝ᵥ y
```

### Optimality Certificate Theorem
If $x^*$ is primal feasible, $y^*$ is dual feasible, and $c^T x^* = b^T y^*$, then:
- For any primal feasible $x$: $c^T x \le b^T y^* = c^T x^*$, proving global maximality of $x^*$.
- For any dual feasible $y$: $b^T y^* = c^T x^* \le b^T y$, proving global minimality of $y^*$.

```lean
theorem optimality_certificate (A : Matrix m n ℝ) (b : m → ℝ) (c : n → ℝ)
    {x_star : n → ℝ} {y_star : m → ℝ}
    (hx_star : PrimalFeasible A b x_star) (hy_star : DualFeasible A c y_star)
    (h_eq : c ⬝ᵥ x_star = b ⬝ᵥ y_star) :
    (∀ x, PrimalFeasible A b x → c ⬝ᵥ x ≤ c ⬝ᵥ x_star) ∧
    (∀ y, DualFeasible A c y → b ⬝ᵥ y_star ≤ b ⬝ᵥ y)
```

### Infeasibility Corollaries
- If the primal is unbounded ($\forall M, \exists x \text{ feasible}, c^T x > M$), then no dual feasible solution can exist (otherwise $c^T x \le b^T y$ would provide an upper bound).
- If the dual is unbounded below, then no primal feasible solution can exist.
