/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# Karger's Randomized Min-Cut Contraction Algorithm

> **Status: stub — not verified** (Phase 4 canon stub; contraction survival product is proven,
> but randomized graph contraction on PMF is a specification stub).

This module formalizes Karger's random contraction algorithm for the global minimum cut
in multigraphs:
1. **Degree & Edge Bounds**: In any graph where every vertex has degree at least the min-cut
   size $k$, Handshaking implies $2|E| = \sum_v \text{deg}(v) \ge n \cdot k$,
   so $|E| \ge n k / 2$.
2. **Single Contraction Survival**: A uniformly chosen random edge avoids a fixed min-cut of
   size $k$ with probability $1 - k / |E| \ge 1 - 2/n = (n-2)/n$.
3. **Telescoping Success Probability**: After $n - 2$ successive contractions, the probability
   that the min-cut survives without any of its edges being contracted is:
   $$\mathbb{P}[\text{success}] \ge \prod_{i=0}^{n-3} \frac{n - i - 2}{n - i} = \frac{2}{n(n-1)}$$
4. **Repetition Amplification**: Repeating the algorithm $T = \binom{n}{2} \ln(1/\delta)$ times
   reduces failure probability below $\delta$.
5. **Operational Complexity**: A single contraction run executes in $O(n^2)$ steps.

## Key Definitions and Theorems
- `Amort.Randomized.minCut_edge_lower_bound`: $n \cdot k \le 2 \cdot |E|$.
- `Amort.Randomized.stepSurvivalProb`: $(n - 2) / n$ survival probability at $n$ vertices.
- `Amort.Randomized.kargerSuccessBound`: $\frac{2}{n(n-1)}$ lower bound.
- `Amort.Randomized.kargerSingleRunBound`: Operational step count $n^2$.
- `Amort.Randomized.kargerTotalBound`: Amplified operational step count $n^4$.
-/

namespace Amort.Randomized

/-- **Degree Sum and Edge Lower Bound**:
In any multigraph with $n$ vertices where every vertex has degree at least $k$,
the Handshaking Lemma implies $n \cdot k \le 2 \cdot |E|$. -/
theorem minCut_edge_lower_bound (n k E : ℕ)
    (deg : ℕ → ℕ)
    (hdeg : ∀ v ∈ Finset.range n, k ≤ deg v)
    (h_handshake : 2 * E = ∑ v ∈ Finset.range n, deg v) :
    n * k ≤ 2 * E := by
  rw [h_handshake]
  have h_sum_le : (∑ v ∈ Finset.range n, k) ≤ ∑ v ∈ Finset.range n, deg v := by
    apply Finset.sum_le_sum
    intro v hv
    exact hdeg v hv
  simp only [Finset.sum_const, nsmul_eq_mul] at h_sum_le
  rw [Finset.card_range] at h_sum_le
  omega

/-- Single contraction step survival probability when contracting from $n$ vertices:
at least $(n - 2) / n$. -/
noncomputable def stepSurvivalProb (n : ℕ) : ℝ :=
  ((n - 2 : ℝ)) / ((n : ℝ))

/-- Survival probability is positive for any $n \ge 3$. -/
lemma stepSurvivalProb_pos {n : ℕ} (hn : 3 ≤ n) :
    0 < stepSurvivalProb n := by
  dsimp [stepSurvivalProb]
  have hnum : (0 : ℝ) < ((n - 2 : ℝ)) := by
    have : (2 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 2 < n)
    linarith
  have hden : (0 : ℝ) < ((n : ℝ)) := by
    have : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    exact this
  exact div_pos hnum hden

/-- The closed-form Karger success probability lower bound $\frac{2}{n(n-1)}$. -/
noncomputable def kargerSuccessBound (n : ℕ) : ℝ :=
  (2 : ℝ) / (((n : ℝ) * ((n : ℝ) - 1)))

/-- For any $n \ge 2$, the success probability lower bound is strictly positive. -/
lemma kargerSuccessBound_pos {n : ℕ} (hn : 2 ≤ n) :
    0 < kargerSuccessBound n := by
  dsimp [kargerSuccessBound]
  have hpos : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by
    have hn1 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hn2 : (0 : ℝ) < (n : ℝ) - 1 := by
      have : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
      linarith
    exact mul_pos hn1 hn2
  exact div_pos (by norm_num) hpos

/-- **Telescoping Product Identity**:
For $n = 3$, survival probability is $(3 - 2)/3 = 1/3 = 2 / (3 \times 2)$. -/
theorem karger_telescoping_base :
    stepSurvivalProb 3 = kargerSuccessBound 3 := by
  dsimp [stepSurvivalProb, kargerSuccessBound]
  norm_num

/-- **Telescoping Step Invariant**:
Multiplying the $(n-1)$-vertex bound by the $n$-vertex survival ratio $(n-2)/n$
telescopes to the $n$-vertex bound:
$$\frac{n - 2}{n} \cdot \frac{2}{(n - 1)(n - 2)} = \frac{2}{n(n - 1)}$$ -/
theorem karger_telescoping_step (n : ℕ) (hn : 3 ≤ n) :
    stepSurvivalProb n * kargerSuccessBound (n - 1) = kargerSuccessBound n := by
  dsimp [stepSurvivalProb, kargerSuccessBound]
  have h_cast1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    have : 1 ≤ n := by omega
    rw [Nat.cast_sub (R := ℝ) this]; push_cast; rfl
  rw [h_cast1]
  have hn_pos : (n : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    linarith
  have h_ne1 : (n : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
    linarith
  have h_ne2 : (n : ℝ) - 1 - 1 ≠ 0 := by
    have : (2 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 2 < n)
    linarith
  field_simp
  ring

/-- Operational step complexity for a single contraction run:
contracting $n - 2$ vertices in $O(n^2)$ steps. -/
def kargerSingleRunBound (n : ℕ) : ℕ :=
  n ^ 2

/-- Operational step complexity for amplified Karger Min-Cut:
running $O(n^2)$ independent trials yields total work $O(n^4)$. -/
def kargerTotalBound (n : ℕ) : ℕ :=
  n ^ 4

/-- Amplified Karger min-cut complexity bound. -/
theorem kargerTotalWork_bound (n : ℕ) :
    kargerTotalBound n ≤ n ^ 4 := by
  rfl

end Amort.Randomized
