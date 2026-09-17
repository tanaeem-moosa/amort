/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Mathlib.Analysis.Asymptotics.Defs

/-!
# Compositional Complexity Algebra

This module formalizes compositional complexity theorems connecting algorithm loop
structures and sequential phases to Mathlib's `Mathlib.Analysis.Asymptotics.IsBigO`
asymptotic framework.

## Mathematical Architecture

1. **Nested Loops (Product Composition)**:
   If an outer loop executes $N(n) = O(g_1(n))$ iterations and each iteration incurs cost
   $C(n) = O(g_2(n))$, the total cost $N(n) \cdot C(n)$ is $O(g_1(n) \cdot g_2(n))$.
   More generally, if total cost satisfies $T(n) \le N(n) \cdot C(n)$ pointwise, then
   $T(n) = O(g_1(n) \cdot g_2(n))$.

2. **Sequential Phases (Sum and Max Composition)**:
   If an algorithm executes phase 1 with cost $T_1(n) = O(g_1(n))$ followed by phase 2
   with cost $T_2(n) = O(g_2(n))$, the combined cost $T_1(n) + T_2(n)$ satisfies:
   - Sum bound: $T_1(n) + T_2(n) = O(g_1(n) + g_2(n))$ for nonnegative $g_1, g_2$.
   - Max bound: $T_1(n) + T_2(n) = O(\max(|g_1(n)|, |g_2(n)|))$.
   - Max phase cost: $\max(T_1(n), T_2(n)) = O(\max(|g_1(n)|, |g_2(n)|))$.

3. **Phase Dominance**:
   If phase 2 is asymptotically dominated by phase 1 ($g_2 = O(g_1)$), then the combined
   cost simplifies to the dominant phase: $T_1(n) + T_2(n) = O(g_1(n))$.

4. **Natural Number Coercion Bridges**:
   Algorithmic complexity often measures integer step counters $N, C, T : \alpha \to \mathbb{N}$.
   Specialized lemmas lift these naturally to real-valued `IsBigO` relations.

## Key Theorems
- `Amort.Recurrence.isBigO_nested_loops`: Product composition for nested loops.
- `Amort.Recurrence.isBigO_of_le_mul`: Pointwise upper-bounded loop cost.
- `Amort.Recurrence.isBigO_sequential_max`: Sum of phases bounded by maximum of asymptotic bounds.
- `Amort.Recurrence.isBigO_sequential_add`: Sum of phases bounded by sum of asymptotic bounds.
- `Amort.Recurrence.isBigO_sequential_dominance`: Dominance rule for sequential phases.
- `Amort.Recurrence.isBigO_nested_loops_nat`: Loop product rule for `ℕ`-valued counters.
- `Amort.Recurrence.isBigO_sequential_add_nat`: Sequential sum rule for `ℕ`-valued counters.
-/

namespace Amort.Recurrence

open Asymptotics

variable {α : Type*} {l : Filter α}

/-! ### Nested Loops (Product Composition) -/

/-- Product composition for nested loops: if outer loop iteration count $N = O(g_1)$
and per-iteration cost $C = O(g_2)$, then the combined cost $N \cdot C = O(g_1 \cdot g_2)$. -/
theorem isBigO_nested_loops (N g₁ C g₂ : α → ℝ)
    (hN : N =O[l] g₁) (hC : C =O[l] g₂) :
    (fun x ↦ N x * C x) =O[l] (fun x ↦ g₁ x * g₂ x) :=
  hN.mul hC

/-- Pointwise bounded loop cost: if total cost $T$ satisfies $0 \le T(x) \le N(x) \cdot C(x)$
eventually, with $N = O(g_1)$ and $C = O(g_2)$, then $T = O(g_1 \cdot g_2)$. -/
theorem isBigO_of_le_mul (T N g₁ C g₂ : α → ℝ)
    (hT_nonneg : ∀ᶠ x in l, 0 ≤ T x)
    (hT_le : ∀ᶠ x in l, T x ≤ N x * C x)
    (hN_nonneg : ∀ᶠ x in l, 0 ≤ N x)
    (hC_nonneg : ∀ᶠ x in l, 0 ≤ C x)
    (hN : N =O[l] g₁) (hC : C =O[l] g₂) :
    T =O[l] (fun x ↦ g₁ x * g₂ x) := by
  have h_prod : (fun x ↦ N x * C x) =O[l] (fun x ↦ g₁ x * g₂ x) := hN.mul hC
  rw [isBigO_iff] at h_prod ⊢
  rcases h_prod with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  filter_upwards [hT_nonneg, hT_le, hN_nonneg, hC_nonneg, hc] with x hx0 hxle hxN hxC hcx
  simp only [Real.norm_eq_abs] at hcx ⊢
  rw [_root_.abs_of_nonneg hx0]
  rw [_root_.abs_of_nonneg (mul_nonneg hxN hxC)] at hcx
  exact le_trans hxle hcx

/-- Product composition for natural-number loop counters coerced to `ℝ`. -/
theorem isBigO_nested_loops_nat (N g₁ C g₂ : α → ℕ)
    (hN : (fun x ↦ ((N x : ℕ) : ℝ)) =O[l] (fun x ↦ ((g₁ x : ℕ) : ℝ)))
    (hC : (fun x ↦ ((C x : ℕ) : ℝ)) =O[l] (fun x ↦ ((g₂ x : ℕ) : ℝ))) :
    (fun x ↦ ((N x * C x : ℕ) : ℝ)) =O[l] (fun x ↦ ((g₁ x * g₂ x : ℕ) : ℝ)) := by
  have h := hN.mul hC
  simp only [Nat.cast_mul] at h ⊢
  exact h

/-- Pointwise bounded natural-number loop cost coerced to `ℝ`. -/
theorem isBigO_of_le_mul_nat (T N g₁ C g₂ : α → ℕ)
    (hT_le : ∀ᶠ x in l, T x ≤ N x * C x)
    (hN : (fun x ↦ ((N x : ℕ) : ℝ)) =O[l] (fun x ↦ ((g₁ x : ℕ) : ℝ)))
    (hC : (fun x ↦ ((C x : ℕ) : ℝ)) =O[l] (fun x ↦ ((g₂ x : ℕ) : ℝ))) :
    (fun x ↦ ((T x : ℕ) : ℝ)) =O[l] (fun x ↦ ((g₁ x * g₂ x : ℕ) : ℝ)) := by
  have h_prod : (fun x ↦ ((N x * C x : ℕ) : ℝ)) =O[l]
      (fun x ↦ ((g₁ x * g₂ x : ℕ) : ℝ)) := isBigO_nested_loops_nat N g₁ C g₂ hN hC
  rw [isBigO_iff] at h_prod ⊢
  rcases h_prod with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  filter_upwards [hT_le, hc] with x hxle hcx
  simp only [Real.norm_eq_abs, Nat.abs_cast] at hcx ⊢
  have hxle_real : ((T x : ℕ) : ℝ) ≤ ((N x * C x : ℕ) : ℝ) := by exact_mod_cast hxle
  exact le_trans hxle_real hcx

/-! ### Sequential Phases (Sum and Max Composition) -/

/-- Auxiliary: left function is bounded by maximum of absolute values. -/
lemma isBigO_left_le_max (g₁ g₂ : α → ℝ) :
    g₁ =O[l] (fun x ↦ max |g₁ x| |g₂ x|) := by
  refine IsBigO.of_bound 1 ?_
  apply Filter.Eventually.of_forall
  intro x
  simp only [Real.norm_eq_abs, one_mul]
  have h1 : |g₁ x| ≤ max |g₁ x| |g₂ x| := le_max_left _ _
  have h2 : 0 ≤ max |g₁ x| |g₂ x| := le_trans (abs_nonneg _) h1
  rw [_root_.abs_of_nonneg h2]
  exact h1

/-- Auxiliary: right function is bounded by maximum of absolute values. -/
lemma isBigO_right_le_max (g₁ g₂ : α → ℝ) :
    g₂ =O[l] (fun x ↦ max |g₁ x| |g₂ x|) := by
  refine IsBigO.of_bound 1 ?_
  apply Filter.Eventually.of_forall
  intro x
  simp only [Real.norm_eq_abs, one_mul]
  have h1 : |g₂ x| ≤ max |g₁ x| |g₂ x| := le_max_right _ _
  have h2 : 0 ≤ max |g₁ x| |g₂ x| := le_trans (abs_nonneg _) h1
  rw [_root_.abs_of_nonneg h2]
  exact h1

/-- Sequential phases max composition: running phase 1 ($T_1 = O(g_1)$) followed by
phase 2 ($T_2 = O(g_2)$) yields combined cost $T_1 + T_2 = O(\max(|g_1|, |g_2|))$. -/
theorem isBigO_sequential_max (T₁ g₁ T₂ g₂ : α → ℝ)
    (hT₁ : T₁ =O[l] g₁) (hT₂ : T₂ =O[l] g₂) :
    (fun x ↦ T₁ x + T₂ x) =O[l] (fun x ↦ max |g₁ x| |g₂ x|) := by
  have h1 : T₁ =O[l] (fun x ↦ max |g₁ x| |g₂ x|) := hT₁.trans (isBigO_left_le_max g₁ g₂)
  have h2 : T₂ =O[l] (fun x ↦ max |g₁ x| |g₂ x|) := hT₂.trans (isBigO_right_le_max g₁ g₂)
  exact h1.add h2

/-- Sequential phases max of costs: $\max(T_1, T_2) = O(\max(|g_1|, |g_2|))$. -/
theorem isBigO_max_of_max (T₁ g₁ T₂ g₂ : α → ℝ)
    (hT₁_nonneg : ∀ᶠ x in l, 0 ≤ T₁ x)
    (hT₂_nonneg : ∀ᶠ x in l, 0 ≤ T₂ x)
    (hT₁ : T₁ =O[l] g₁) (hT₂ : T₂ =O[l] g₂) :
    (fun x ↦ max (T₁ x) (T₂ x)) =O[l] (fun x ↦ max |g₁ x| |g₂ x|) := by
  have h_sum := isBigO_sequential_max T₁ g₁ T₂ g₂ hT₁ hT₂
  rw [isBigO_iff] at h_sum ⊢
  rcases h_sum with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  filter_upwards [hT₁_nonneg, hT₂_nonneg, hc] with x hx1 hx2 hcx
  simp only [Real.norm_eq_abs] at hcx ⊢
  have h_max_pos : 0 ≤ max (T₁ x) (T₂ x) := le_trans hx1 (le_max_left _ _)
  rw [_root_.abs_of_nonneg h_max_pos]
  rw [_root_.abs_of_nonneg (add_nonneg hx1 hx2)] at hcx
  have h_le_sum : max (T₁ x) (T₂ x) ≤ T₁ x + T₂ x := by
    rcases le_total (T₁ x) (T₂ x) with hle | hle
    · rw [max_eq_right hle]; linarith
    · rw [max_eq_left hle]; linarith
  exact le_trans h_le_sum hcx

/-- Sequential phases sum bound for nonnegative $g_1, g_2$:
$T_1(x) + T_2(x) = O(g_1(x) + g_2(x))$. -/
theorem isBigO_sequential_add (T₁ g₁ T₂ g₂ : α → ℝ)
    (hg₁ : ∀ᶠ x in l, 0 ≤ g₁ x) (hg₂ : ∀ᶠ x in l, 0 ≤ g₂ x)
    (hT₁ : T₁ =O[l] g₁) (hT₂ : T₂ =O[l] g₂) :
    (fun x ↦ T₁ x + T₂ x) =O[l] (fun x ↦ g₁ x + g₂ x) := by
  have h1 : g₁ =O[l] (fun x ↦ g₁ x + g₂ x) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [hg₁, hg₂] with x hx₁ hx₂
    simp only [Real.norm_eq_abs, one_mul]
    rw [_root_.abs_of_nonneg hx₁, _root_.abs_of_nonneg (add_nonneg hx₁ hx₂)]
    exact le_add_of_nonneg_right hx₂
  have h2 : g₂ =O[l] (fun x ↦ g₁ x + g₂ x) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [hg₁, hg₂] with x hx₁ hx₂
    simp only [Real.norm_eq_abs, one_mul]
    rw [_root_.abs_of_nonneg hx₂, _root_.abs_of_nonneg (add_nonneg hx₁ hx₂)]
    exact le_add_of_nonneg_left hx₁
  exact (hT₁.trans h1).add (hT₂.trans h2)

/-- Sequential sum rule for natural-number step counters coerced to `ℝ`. -/
theorem isBigO_sequential_add_nat (T₁ g₁ T₂ g₂ : α → ℕ)
    (hT₁ : (fun x ↦ ((T₁ x : ℕ) : ℝ)) =O[l] (fun x ↦ ((g₁ x : ℕ) : ℝ)))
    (hT₂ : (fun x ↦ ((T₂ x : ℕ) : ℝ)) =O[l] (fun x ↦ ((g₂ x : ℕ) : ℝ))) :
    (fun x ↦ ((T₁ x + T₂ x : ℕ) : ℝ)) =O[l] (fun x ↦ ((g₁ x + g₂ x : ℕ) : ℝ)) := by
  have h1 : (fun x ↦ ((g₁ x : ℕ) : ℝ)) =O[l] (fun x ↦ ((g₁ x + g₂ x : ℕ) : ℝ)) := by
    refine IsBigO.of_bound 1 ?_
    apply Filter.Eventually.of_forall
    intro x
    simp only [Real.norm_eq_abs, Nat.abs_cast, one_mul]
    have : g₁ x ≤ g₁ x + g₂ x := Nat.le_add_right _ _
    exact_mod_cast this
  have h2 : (fun x ↦ ((g₂ x : ℕ) : ℝ)) =O[l] (fun x ↦ ((g₁ x + g₂ x : ℕ) : ℝ)) := by
    refine IsBigO.of_bound 1 ?_
    apply Filter.Eventually.of_forall
    intro x
    simp only [Real.norm_eq_abs, Nat.abs_cast, one_mul]
    have : g₂ x ≤ g₁ x + g₂ x := Nat.le_add_left _ _
    exact_mod_cast this
  have h := (hT₁.trans h1).add (hT₂.trans h2)
  simp only [Nat.cast_add] at h ⊢
  exact h

/-- Pointwise bounded sequential cost: if $0 \le T(x) \le T_1(x) + T_2(x)$ eventually,
with $T_1 = O(g_1)$ and $T_2 = O(g_2)$, then $T = O(\max(|g_1|, |g_2|))$. -/
theorem isBigO_of_le_add (T T₁ g₁ T₂ g₂ : α → ℝ)
    (hT_nonneg : ∀ᶠ x in l, 0 ≤ T x)
    (hT_le : ∀ᶠ x in l, T x ≤ T₁ x + T₂ x)
    (hT₁_nonneg : ∀ᶠ x in l, 0 ≤ T₁ x)
    (hT₂_nonneg : ∀ᶠ x in l, 0 ≤ T₂ x)
    (hT₁ : T₁ =O[l] g₁) (hT₂ : T₂ =O[l] g₂) :
    T =O[l] (fun x ↦ max |g₁ x| |g₂ x|) := by
  have h_sum := isBigO_sequential_max T₁ g₁ T₂ g₂ hT₁ hT₂
  rw [isBigO_iff] at h_sum ⊢
  rcases h_sum with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  filter_upwards [hT_nonneg, hT_le, hT₁_nonneg, hT₂_nonneg, hc] with x hx0 hxle hx1 hx2 hcx
  simp only [Real.norm_eq_abs] at hcx ⊢
  rw [_root_.abs_of_nonneg hx0]
  rw [_root_.abs_of_nonneg (add_nonneg hx1 hx2)] at hcx
  exact le_trans hxle hcx

/-! ### Phase Dominance -/

/-- Dominance for functions: if $g_2 = O(g_1)$, then $g_1 + g_2 = O(g_1)$. -/
theorem isBigO_add_of_isBigO (g₁ g₂ : α → ℝ) (h : g₂ =O[l] g₁) :
    (fun x ↦ g₁ x + g₂ x) =O[l] g₁ :=
  (isBigO_refl g₁ l).add h

/-- Phase dominance: if phase 2 is asymptotically dominated by phase 1 ($g_2 = O(g_1)$),
then running phase 1 followed by phase 2 yields combined complexity $O(g_1)$. -/
theorem isBigO_sequential_dominance (T₁ g₁ T₂ g₂ : α → ℝ)
    (hT₁ : T₁ =O[l] g₁) (hT₂ : T₂ =O[l] g₂) (hg : g₂ =O[l] g₁) :
    (fun x ↦ T₁ x + T₂ x) =O[l] g₁ :=
  hT₁.add (hT₂.trans hg)

end Amort.Recurrence
