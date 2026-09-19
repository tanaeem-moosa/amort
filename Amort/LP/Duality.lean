/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Linear Programming Duality: Weak Duality and Optimality Certificates

This module formalizes linear programs in standard inequality form over finite-dimensional
real vector spaces (`Fin m → ℝ`, `Fin n → ℝ`), establishes the Weak Duality Theorem, proves the
Optimality Certificate Theorem, and deduces infeasibility corollaries for unbounded programs.

## Mathematical Architecture

1. **Standard Inequality Form LP**:
   - Given constraint matrix $A \in \mathbb{R}^{m \times n}$, right-hand side vector
     $b \in \mathbb{R}^m$, and objective vector $c \in \mathbb{R}^n$:
     - **Primal LP**: maximize $c^T x$ subject to $A x \le b$ and $x \ge 0$.
     - **Dual LP**: minimize $b^T y$ subject to $A^T y \ge c$ and $y \ge 0$.

2. **Feasibility Predicates**:
   - `PrimalFeasible A b x`: $0 \le x \land A x \le b$.
   - `DualFeasible A c y`: $0 \le y \land c \le A^T y$.

3. **Weak Duality Theorem**:
   For any primal feasible vector $x$ and dual feasible vector $y$:
   $$c^T x \le (A^T y)^T x = y^T (A x) \le y^T b = b^T y$$
   The objective value of any primal feasible solution provides a lower bound on the objective
   value of any dual feasible solution.

4. **Optimality Certificate Theorem**:
   If primal feasible $x^*$ and dual feasible $y^*$ satisfy $c^T x^* = b^T y^*$,
   then $x^*$ achieves the global maximum of the primal problem and $y^*$ achieves the global
   minimum of the dual problem.

5. **Infeasibility Corollaries**:
   - If the primal problem is unbounded from above, the dual problem is infeasible.
   - If the dual problem is unbounded from below, the primal problem is infeasible.

## Key Definitions and Theorems
- `Amort.LP.PrimalFeasible`: Primal feasibility predicate.
- `Amort.LP.DualFeasible`: Dual feasibility predicate.
- `Amort.LP.dotProduct_le_dotProduct_of_nonneg_right`: Monotonicity of dot product on non-negatives.
- `Amort.LP.weak_duality`: Weak Duality Theorem ($c^T x \le b^T y$).
- `Amort.LP.optimality_certificate`: Certificate ($c^T x^* = b^T y^* \implies \text{OPT}$).
- `Amort.LP.dual_infeasible_of_unbounded_primal`: Unbounded primal $\implies$ dual infeasibility.
- `Amort.LP.primal_infeasible_of_unbounded_dual`: Unbounded dual $\implies$ primal infeasibility.
-/

open Matrix

namespace Amort.LP

variable {m n : Type} [Fintype m] [Fintype n]

/-! ### Primal and Dual Formulations -/

/-- Primal feasibility predicate: $x \ge 0$ and $A x \le b$. -/
def PrimalFeasible (A : Matrix m n ℝ) (b : m → ℝ) (x : n → ℝ) : Prop :=
  0 ≤ x ∧ A.mulVec x ≤ b

/-- Dual feasibility predicate: $y \ge 0$ and $A^T y \ge c$. -/
def DualFeasible (A : Matrix m n ℝ) (c : n → ℝ) (y : m → ℝ) : Prop :=
  0 ≤ y ∧ c ≤ A.transpose.mulVec y

/-! ### Dot Product Inequalities -/

/-- Dot product is monotone in its left argument when the right argument is non-negative. -/
lemma dotProduct_le_dotProduct_of_nonneg_right {k : Type} [Fintype k] {u v w : k → ℝ}
    (huv : u ≤ v) (hw : 0 ≤ w) :
    u ⬝ᵥ w ≤ v ⬝ᵥ w := by
  dsimp [dotProduct]
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_right (huv i) (hw i)

/-- Dot product transpose duality identity: $y^T (A x) = (A^T y)^T x$. -/
lemma dotProduct_mulVec_eq_mulVec_transpose (A : Matrix m n ℝ) (y : m → ℝ) (x : n → ℝ) :
    y ⬝ᵥ (A.mulVec x) = (A.transpose.mulVec y) ⬝ᵥ x := by
  rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]

/-! ### Weak Duality Theorem -/

/-- The Weak Duality Theorem: For any primal feasible solution $x$ and dual feasible solution $y$,
the primal objective $c^T x$ is bounded above by the dual objective $b^T y$:
$$c^T x \le (A^T y)^T x = y^T (A x) \le y^T b = b^T y$$ -/
theorem weak_duality (A : Matrix m n ℝ) (b : m → ℝ) (c : n → ℝ)
    {x : n → ℝ} {y : m → ℝ}
    (hx : PrimalFeasible A b x) (hy : DualFeasible A c y) :
    c ⬝ᵥ x ≤ b ⬝ᵥ y := by
  have h1 : c ⬝ᵥ x ≤ (A.transpose.mulVec y) ⬝ᵥ x :=
    dotProduct_le_dotProduct_of_nonneg_right hy.2 hx.1
  have h2 : (A.transpose.mulVec y) ⬝ᵥ x = y ⬝ᵥ (A.mulVec x) := by
    rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]
  have h3 : y ⬝ᵥ (A.mulVec x) ≤ y ⬝ᵥ b := by
    rw [dotProduct_comm y (A.mulVec x), dotProduct_comm y b]
    exact dotProduct_le_dotProduct_of_nonneg_right hx.2 hy.1
  have h4 : y ⬝ᵥ b = b ⬝ᵥ y := dotProduct_comm y b
  linarith

/-! ### Optimality Certificates -/

/-- Optimality Certificate Theorem: If primal feasible $x^*$ and dual feasible $y^*$ satisfy
$c^T x^* = b^T y^*$, then $x^*$ achieves the maximum of the primal problem and $y^*$ achieves
the minimum of the dual problem. -/
theorem optimality_certificate (A : Matrix m n ℝ) (b : m → ℝ) (c : n → ℝ)
    {x_star : n → ℝ} {y_star : m → ℝ}
    (hx_star : PrimalFeasible A b x_star) (hy_star : DualFeasible A c y_star)
    (h_eq : c ⬝ᵥ x_star = b ⬝ᵥ y_star) :
    (∀ x, PrimalFeasible A b x → c ⬝ᵥ x ≤ c ⬝ᵥ x_star) ∧
    (∀ y, DualFeasible A c y → b ⬝ᵥ y_star ≤ b ⬝ᵥ y) := by
  constructor
  · intro x hx
    have h_bound := weak_duality A b c hx hy_star
    linarith
  · intro y hy
    have h_bound := weak_duality A b c hx_star hy
    linarith

/-- Primal optimality certificate: Equality of objective values certifies primal maximality. -/
theorem primal_optimal_of_certificate (A : Matrix m n ℝ) (b : m → ℝ) (c : n → ℝ)
    {x_star : n → ℝ} {y_star : m → ℝ}
    (hx_star : PrimalFeasible A b x_star) (hy_star : DualFeasible A c y_star)
    (h_eq : c ⬝ᵥ x_star = b ⬝ᵥ y_star) :
    ∀ x, PrimalFeasible A b x → c ⬝ᵥ x ≤ c ⬝ᵥ x_star :=
  (optimality_certificate A b c hx_star hy_star h_eq).1

/-- Dual optimality certificate: Equality of objective values certifies dual minimality. -/
theorem dual_optimal_of_certificate (A : Matrix m n ℝ) (b : m → ℝ) (c : n → ℝ)
    {x_star : n → ℝ} {y_star : m → ℝ}
    (hx_star : PrimalFeasible A b x_star) (hy_star : DualFeasible A c y_star)
    (h_eq : c ⬝ᵥ x_star = b ⬝ᵥ y_star) :
    ∀ y, DualFeasible A c y → b ⬝ᵥ y_star ≤ b ⬝ᵥ y :=
  (optimality_certificate A b c hx_star hy_star h_eq).2

/-! ### Infeasibility Corollaries -/

/-- Primal unboundedness predicate: For every bound $M$, there exists a primal feasible solution
achieving objective value greater than $M$. -/
def PrimalUnbounded (A : Matrix m n ℝ) (b : m → ℝ) (c : n → ℝ) : Prop :=
  ∀ M : ℝ, ∃ x, PrimalFeasible A b x ∧ M < c ⬝ᵥ x

/-- Dual unboundedness predicate: For every bound $M$, there exists a dual feasible solution
achieving objective value strictly less than $M$. -/
def DualUnbounded (A : Matrix m n ℝ) (b : m → ℝ) (c : n → ℝ) : Prop :=
  ∀ M : ℝ, ∃ y, DualFeasible A c y ∧ b ⬝ᵥ y < M

/-- Corollary: If the primal LP is unbounded, then the dual LP is infeasible (has no solutions). -/
theorem dual_infeasible_of_unbounded_primal (A : Matrix m n ℝ) (b : m → ℝ) (c : n → ℝ)
    (hunb : PrimalUnbounded A b c) :
    ¬ ∃ y, DualFeasible A c y := by
  rintro ⟨y, hy⟩
  obtain ⟨x, hx, hgt⟩ := hunb (b ⬝ᵥ y)
  have hwd := weak_duality A b c hx hy
  linarith

/-- Corollary: If the dual LP is unbounded, then the primal LP is infeasible (has no solutions). -/
theorem primal_infeasible_of_unbounded_dual (A : Matrix m n ℝ) (b : m → ℝ) (c : n → ℝ)
    (hunb : DualUnbounded A b c) :
    ¬ ∃ x, PrimalFeasible A b x := by
  rintro ⟨x, hx⟩
  obtain ⟨y, hy, hlt⟩ := hunb (c ⬝ᵥ x)
  have hwd := weak_duality A b c hx hy
  linarith

end Amort.LP
