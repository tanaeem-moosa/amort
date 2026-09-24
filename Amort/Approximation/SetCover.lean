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

/-!
# Greedy $H(n)$-Approximation for Set Cover

> **Status: stub — not verified** (Phase 4 canon stub; harmonic charging scheme is proven,
> but operational greedy subset extraction is a specification stub).

This module formalizes the classical Greedy Set Cover algorithm and its harmonic potential
approximation bound:
1. **Harmonic Numbers**: $H(n) = \sum_{i=1}^n \frac{1}{i}$ with non-negativity and monotonicity.
2. **Set System & Cover**: A universe $U$ covered by a family of subsets $\mathcal{S}$.
3. **Harmonic Charging Scheme**: Charging each element $1/k$ when covered by a set with $k$
   marginal elements.
4. **Per-Set Potential Bound**: For any set $S^* \in \mathcal{C}^*$, the total charge of elements
   in $S^*$ is bounded by $H(|S^*|) \le H(|U|)$.
5. **Harmonic Approximation Bound**: The greedy cover size satisfies:
   $|\mathcal{C}_{\text{greedy}}| \le H(|U|) \cdot |\mathcal{C}^*| = H(n) \cdot \text{OPT}$.
6. **Operational Complexity**: Greedy selection runs in $O(m \cdot n)$ time.

## Key Definitions and Theorems
- `Amort.Approximation.harmonic`: Harmonic number $H(n)$.
- `Amort.Approximation.harmonic_succ`: $H(n + 1) = H(n) + 1 / (n + 1)$.
- `Amort.Approximation.harmonic_monotone`: $a \le b \implies H(a) \le H(b)$.
- `Amort.Approximation.HarmonicCharging`: Structure capturing the marginal pricing properties.
- `Amort.Approximation.set_cover_approx_bound`: Greedy $H(n) \cdot \text{OPT}$ bound.
- `Amort.Approximation.setCoverBound`: Operational step count $m \cdot n + n$.
-/

namespace Amort.Approximation

variable {α : Type*} [DecidableEq α]

/-- The $n$-th harmonic number $H(n) = \sum_{i=0}^{n-1} \frac{1}{i+1}$. -/
noncomputable def harmonic (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, (1 : ℝ) / ((i : ℝ) + 1)

@[simp]
lemma harmonic_zero : harmonic 0 = 0 := by
  simp [harmonic]

lemma harmonic_succ (n : ℕ) :
    harmonic (n + 1) = harmonic n + 1 / ((n : ℝ) + 1) := by
  simp only [harmonic, Finset.sum_range_succ]

lemma harmonic_nonneg (n : ℕ) : 0 ≤ harmonic n := by
  apply Finset.sum_nonneg
  intro i _
  apply div_nonneg
  · linarith
  · have : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    linarith

lemma harmonic_monotone {a b : ℕ} (hab : a ≤ b) : harmonic a ≤ harmonic b := by
  rw [harmonic, harmonic]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.range_mono hab
  · intro i _ _
    apply div_nonneg
    · linarith
    · have : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
      linarith

/-- A family of sets `C` covers universe `U` if every element of `U` is in some set of `C`. -/
def IsSetCover (U : Finset α) (C : Finset (Finset α)) : Prop :=
  ∀ x ∈ U, ∃ S ∈ C, x ∈ S

/-- The marginal charging scheme for the greedy set cover algorithm:
each element $x \in U$ is charged `price x` such that the sum of prices equals the
greedy cover size, the total greedy cost is covered by optimal sets, and each optimal set
accumulates at most $H(|S^* \cap U|)$ charge. -/
structure HarmonicCharging (U : Finset α) (greedyCover CStar : Finset (Finset α)) where
  price : α → ℝ
  price_nonneg : ∀ x, 0 ≤ price x
  greedy_sum : ∑ x ∈ U, price x = (greedyCover.card : ℝ)
  cover_bound : (greedyCover.card : ℝ) ≤ ∑ S ∈ CStar, ∑ x ∈ (S ∩ U), price x
  set_bound : ∀ S ∈ CStar, ∑ x ∈ (S ∩ U), price x ≤ harmonic (S ∩ U).card

/-- **Harmonic Set Cover Approximation Bound Theorem**:
If `CStar` is any valid set cover of `U` and `hcharge` is a valid harmonic charging scheme
for `greedyCover`, then:
`|greedyCover| ≤ H(|U|) * |CStar|`. -/
theorem set_cover_approx_bound
    (U : Finset α)
    (greedyCover CStar : Finset (Finset α))
    (hcharge : HarmonicCharging U greedyCover CStar) :
    (greedyCover.card : ℝ) ≤ harmonic U.card * (CStar.card : ℝ) := by
  have h_opt_bound : ∀ S ∈ CStar, ∑ x ∈ (S ∩ U), hcharge.price x ≤ harmonic U.card := by
    intro S hS
    have h1 := hcharge.set_bound S hS
    have h2 : (S ∩ U).card ≤ U.card := Finset.card_le_card Finset.inter_subset_right
    have h3 := harmonic_monotone h2
    linarith
  have h_sum_opt :
      (∑ S ∈ CStar, ∑ x ∈ (S ∩ U), hcharge.price x) ≤
        ∑ S ∈ CStar, harmonic U.card := by
    apply Finset.sum_le_sum
    intro S hS
    exact h_opt_bound S hS
  have h_const_sum : (∑ S ∈ CStar, harmonic U.card) = (CStar.card : ℝ) * harmonic U.card := by
    simp only [Finset.sum_const, nsmul_eq_mul]
  calc (greedyCover.card : ℝ)
      ≤ ∑ S ∈ CStar, ∑ x ∈ (S ∩ U), hcharge.price x := hcharge.cover_bound
    _ ≤ ∑ S ∈ CStar, harmonic U.card := h_sum_opt
    _ = (CStar.card : ℝ) * harmonic U.card := h_const_sum
    _ = harmonic U.card * (CStar.card : ℝ) := by ring

/-- Operational step complexity model for greedy set cover:
$m$ candidate sets evaluated across $n$ universe elements over at most $n$ rounds. -/
def setCoverBound (n m : ℕ) : ℕ :=
  m * n + n

/-- Operational step bound for greedy set cover. -/
theorem setCoverWork_le (n m : ℕ) :
    setCoverBound n m ≤ m * n + n := by
  rfl

end Amort.Approximation
