/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Linarith

/-!
# Simplex Slack Form and Dictionary Feasibility Invariants

This module formalizes the simplex slack form, dictionary representations, basic solutions,
and the fundamental pivot invariant preservation theorem:
- A linear program in slack form partitions variables into basic indices $B$ and non-basic
  indices $N$.
- Basic variables are expressed as $x_B = \bar{b} - \bar{A} x_N$, and the objective as
  $z = v + \bar{c}^T x_N$.
- A dictionary is feasible if $\bar{b} \ge 0$, which implies the basic solution
  $(x_B, x_N) = (\bar{b}, 0)$ is non-negative.
- The minimum ratio test chooses a leaving variable $l \in B$ such that
  $\theta = \bar{b}_l / \bar{a}_{le} \le \bar{b}_i / \bar{a}_{ie}$ for all $i$ with
  $\bar{a}_{ie} > 0$.
- We prove that any pivot step satisfying the ratio test preserves non-negativity of all
  basic variables, and that the objective value increases whenever $\bar{c}_e > 0$ and $\theta > 0$.

## Mathematical Architecture

1. `Dictionary B N`: Bundles constant vector $\bar{b}$, constraint matrix $\bar{A}$,
   base objective value $v$, and cost vector $\bar{c}$.
2. `Dictionary.IsFeasible`: Invariant predicate $\forall i \in B, 0 \le \bar{b}_i$.
3. `Dictionary.basicSol`: Basic solution mapping non-basics to $0$ and basics to $\bar{b}$.
4. `Dictionary.pivotBasicVal`: Updated basic variable value under step size $\theta$.
5. `Dictionary.pivot_preserves_feasibility`: Proves $0 \le \bar{b}_i - \bar{a}_{ie} \theta$.
6. `Dictionary.new_b_bar_nonneg`: Invariant preservation for new dictionary constant terms.
7. `Dictionary.obj_increases_of_pivot`: Objective progression theorem under positive pivot step.
8. `simplexPivotWork`: Operational arithmetic step counter per pivot step ($O(m \cdot n)$).
-/

open BigOperators

namespace Amort.LP

/-- Simplex dictionary in slack form partitioning variables into basic set $B$ and
non-basic set $N$. -/
structure Dictionary (B N : Type) [Fintype B] [Fintype N] where
  /-- Right-hand side constants for basic variables. -/
  b_bar : B → ℝ
  /-- Matrix coefficients relating basic variables to non-basic variables. -/
  A_bar : B → N → ℝ
  /-- Current objective value at the basic solution. -/
  v : ℝ
  /-- Reduced cost coefficients of non-basic variables. -/
  c_bar : N → ℝ

namespace Dictionary

variable {B N : Type} [Fintype B] [Fintype N]

/-- A dictionary is feasible if all basic constant values are non-negative. -/
def IsFeasible (D : Dictionary B N) : Prop :=
  ∀ i : B, 0 ≤ D.b_bar i

/-- Evaluates basic variables given non-basic variable assignments. -/
def evalBasic (D : Dictionary B N) (xN : N → ℝ) (i : B) : ℝ :=
  D.b_bar i - ∑ j : N, D.A_bar i j * xN j

/-- The canonical basic dictionary solution setting non-basic variables to 0. -/
def basicSol (D : Dictionary B N) : B → ℝ :=
  D.b_bar

/-- The basic solution is non-negative if and only if the dictionary is feasible. -/
theorem basicSol_nonneg_iff (D : Dictionary B N) :
    (∀ i, 0 ≤ D.basicSol i) ↔ D.IsFeasible :=
  Iff.rfl

/-- Evaluates the objective function value for given non-basic variable assignments. -/
def evalObj (D : Dictionary B N) (xN : N → ℝ) : ℝ :=
  D.v + ∑ j : N, D.c_bar j * xN j

/-- Under a pivot step with entering variable $e$, the basic variable value after
setting $x_e = \theta$ and all other non-basic variables to $0$. -/
def pivotBasicVal (D : Dictionary B N) (e : N) (theta : ℝ) (i : B) : ℝ :=
  D.b_bar i - D.A_bar i e * theta

/-- Invariant preservation theorem: If step size $\theta \ge 0$ respects the minimum ratio
bound $\theta \le \bar{b}_i / \bar{a}_{ie}$ for all $i$ with $\bar{a}_{ie} > 0$, then every
basic variable remains non-negative after the pivot step. -/
theorem pivot_preserves_feasibility (D : Dictionary B N) (hD : D.IsFeasible)
    (e : N) (theta : ℝ) (h_theta_nonneg : 0 ≤ theta)
    (h_ratio : ∀ i : B, 0 < D.A_bar i e → theta ≤ D.b_bar i / D.A_bar i e) :
    ∀ i : B, 0 ≤ D.pivotBasicVal e theta i := by
  intro i
  dsimp [pivotBasicVal]
  by_cases hpos : 0 < D.A_bar i e
  · have hr := h_ratio i hpos
    have hmul : D.A_bar i e * theta ≤ D.A_bar i e * (D.b_bar i / D.A_bar i e) :=
      mul_le_mul_of_nonneg_left hr (le_of_lt hpos)
    rw [mul_div_cancel₀ _ (ne_of_gt hpos)] at hmul
    linarith
  · have hnonpos : D.A_bar i e ≤ 0 := by linarith
    have h_prod_nonpos : D.A_bar i e * theta ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hnonpos h_theta_nonneg
    have hb := hD i
    linarith

/-- Invariant preservation for new dictionary constant coefficients:
Given leaving row $l \in B$ with $\bar{a}_{le} > 0$, the new basic constant $\bar{b}'_i$
remains non-negative for every basic row $i$. -/
theorem new_b_bar_nonneg (b_i a_ie b_l a_le : ℝ)
    (hb_i : 0 ≤ b_i) (hb_l : 0 ≤ b_l) (ha_le : 0 < a_le)
    (hratio : 0 < a_ie → b_l / a_le ≤ b_i / a_ie) :
    0 ≤ b_i - a_ie * (b_l / a_le) := by
  by_cases hpos : 0 < a_ie
  · have hr := hratio hpos
    have hmul : a_ie * (b_l / a_le) ≤ a_ie * (b_i / a_ie) :=
      mul_le_mul_of_nonneg_left hr (le_of_lt hpos)
    rw [mul_div_cancel₀ _ (ne_of_gt hpos)] at hmul
    linarith
  · have hnonpos : a_ie ≤ 0 := by linarith
    have h_ratio_nonneg : 0 ≤ b_l / a_le := div_nonneg hb_l (le_of_lt ha_le)
    have hprod : a_ie * (b_l / a_le) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hnonpos h_ratio_nonneg
    linarith

/-- Objective progression theorem: If entering coefficient $\bar{c}_e > 0$ and step $\theta > 0$,
the objective strictly increases. -/
theorem obj_increases_of_pivot (D : Dictionary B N) (e : N) (theta : ℝ)
    (he : 0 < D.c_bar e) (htheta : 0 < theta) :
    D.v < D.v + D.c_bar e * theta := by
  have hprod : 0 < D.c_bar e * theta := mul_pos he htheta
  linarith

end Dictionary

/-! ### Operational Step Complexity Model -/

/-- Operational arithmetic step counter for a single simplex pivot step on an $m \times n$
dictionary: updating $m \times n$ matrix entries, $m$ right-hand side constants, and $n$
objective coefficients. -/
def simplexPivotWork (m n : ℕ) : ℕ :=
  m * n + m + n

/-- Operational arithmetic step counter for verifying primal and dual feasibility
on an $m \times n$ system ($m \cdot n$ multiplications and checks). -/
def lpFeasibilityWork (m n : ℕ) : ℕ :=
  2 * (m * n + m + n)

/-- Upper bound on simplex pivot step work: $m \cdot n + m + n \le (m + 1)(n + 1)$. -/
theorem simplexPivotWork_le (m n : ℕ) :
    simplexPivotWork m n ≤ (m + 1) * (n + 1) := by
  dsimp [simplexPivotWork]
  nlinarith

end Amort.LP
