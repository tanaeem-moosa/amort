/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Amort.Sorting.DecisionTree
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Information-Theoretic Lower Bound for Comparison-Based Sorting

This module formalizes the information-theoretic lower bound for comparison-based sorting
($\Omega(n \log n)$) in Lean 4.

## Mathematical Architecture

1. **Permutation Comparison Model**:
   Sorting algorithms on $n$ elements (represented by `Fin n`) query comparisons between pairs
   of indices $(i, j)$. An input permutation $\sigma \in S_n$ induces the comparison oracle
   `permOracle σ (i, j) := decide (σ i ≤ σ j)`.

2. **Permutation Coverage**:
   Any algorithm that correctly sorts $n$ elements must distinguish all $n!$ input permutations:
   $$\sigma_1 \ne \sigma_2 \implies \text{eval } T\ (\text{permOracle } \sigma_1) \ne
   \text{eval } T\ (\text{permOracle } \sigma_2)$$
   Consequently, the reachable leaves of $T$ must cover all $n!$ distinct outcomes:
   $$n! \le |leaves(T)| \le \text{leafCount}(T) \le 2^{\text{depth}(T)}$$

3. **Concrete Lower Bound**:
   Taking the binary ceiling logarithm yields the worst-case query lower bound:
   $$\text{Nat.clog } 2\ (n!) \le \text{depth}(T)$$

4. **Factorial Combinatorial & Asymptotic Bounds**:
   - Combinatorial lower bound: $(n / 2)^{n / 2} \le n!$.
   - Asymptotic equivalence: $\log(n!) = \Theta(n \log n)$ under `Filter.atTop`.
   - Lower bound dominance: $n \log n = O(\log(n!))$ and $n \log n = O(\text{Nat.clog } 2\ (n!))$.
   - For any family of correct sorting trees, $n \log n = O(\text{depth } T_n)$.

## Key Theorems
- `Amort.Sorting.factorial_le_card_leaves`: $n! \le |leaves(T)|$.
- `Amort.Sorting.factorial_le_leafCount`: $n! \le \text{leafCount}(T)$.
- `Amort.Sorting.factorial_le_two_pow_depth`: $n! \le 2^{\text{depth}(T)}$.
- `Amort.Sorting.clog_factorial_le_depth`: $\text{Nat.clog } 2\ (n!) \le \text{depth}(T)$.
- `Amort.Sorting.pow_div_two_le_factorial`: $(n/2)^{n/2} \le n!$.
- `Amort.Sorting.isBigO_n_log_n_factorial`: $n \log n = O(\log(n!))$.
- `Amort.Sorting.isBigO_factorial_n_log_n`: $\log(n!) = O(n \log n)$.
- `Amort.Sorting.isTheta_factorial_n_log_n`: $\log(n!) = \Theta(n \log n)$.
- `Amort.Sorting.isBigO_n_log_n_clog_factorial`: $n \log n = O(\text{Nat.clog } 2\ (n!))$.
- `Amort.Sorting.isBigO_n_log_n_depth`: $n \log n = O(\text{depth } T_n)$.
-/

namespace Amort.Sorting

open Asymptotics

variable {n : ℕ}

/-- Comparison oracle for elements indexed by `Fin n` under a permutation `σ`. -/
def permOracle (σ : Equiv.Perm (Fin n)) (q : Fin n × Fin n) : Bool :=
  decide (σ q.1 ≤ σ q.2)

/-- A decision tree distinguishes all permutations if its evaluation map on
permutation oracles is injective. -/
def DistinguishesPermutations {β : Type*} (T : DecisionTree (Fin n × Fin n) β) : Prop :=
  Function.Injective (fun σ : Equiv.Perm (Fin n) ↦ DecisionTree.eval T (permOracle σ))

/-- A decision tree is a sorting tree if on each input permutation `σ`, it outputs
the inverse permutation `σ⁻¹` that restores sorted order. -/
def IsSortingTree (T : DecisionTree (Fin n × Fin n) (Equiv.Perm (Fin n))) : Prop :=
  ∀ σ : Equiv.Perm (Fin n), DecisionTree.eval T (permOracle σ) = σ⁻¹

/-- Any sorting tree that outputs `σ⁻¹` distinguishes all permutations. -/
theorem distinguishesPermutations_of_isSortingTree
    (T : DecisionTree (Fin n × Fin n) (Equiv.Perm (Fin n))) (hT : IsSortingTree T) :
    DistinguishesPermutations T := by
  intro σ₁ σ₂ heq
  dsimp at heq
  have h1 : DecisionTree.eval T (permOracle σ₁) = σ₁⁻¹ := hT σ₁
  have h2 : DecisionTree.eval T (permOracle σ₂) = σ₂⁻¹ := hT σ₂
  rw [h1, h2] at heq
  exact inv_inj.mp heq

/-! ### Permutation Coverage and Tree Depth Bounds -/

variable {β : Type*}

/-- Permutation coverage: any decision tree distinguishing all permutations on `n` elements
must have at least `n!` reachable leaves. -/
theorem factorial_le_card_leaves [DecidableEq β] (T : DecisionTree (Fin n × Fin n) β)
    (hT : DistinguishesPermutations T) :
    Nat.factorial n ≤ (DecisionTree.leaves T).card := by
  let f : Equiv.Perm (Fin n) → β := fun σ ↦ DecisionTree.eval T (permOracle σ)
  have hf_inj : Function.Injective f := hT
  have h_img_sub : Finset.image f Finset.univ ⊆ DecisionTree.leaves T := by
    intro b hb
    rcases Finset.mem_image.mp hb with ⟨σ, _, rfl⟩
    exact DecisionTree.eval_mem_leaves T (permOracle σ)
  have h_card_img : (Finset.image f Finset.univ).card = Nat.factorial n := by
    rw [Finset.card_image_of_injective _ hf_inj, Finset.card_univ,
      Fintype.card_perm, Fintype.card_fin]
  rw [← h_card_img]
  exact Finset.card_le_card h_img_sub

/-- Any decision tree distinguishing all permutations has leaf count at least `n!`. -/
theorem factorial_le_leafCount (T : DecisionTree (Fin n × Fin n) β)
    (hT : DistinguishesPermutations T) :
    Nat.factorial n ≤ DecisionTree.leafCount T := by
  classical
  exact (factorial_le_card_leaves T hT).trans (DecisionTree.card_leaves_le_leafCount T)

/-- Any decision tree distinguishing all permutations satisfies `n! ≤ 2 ^ depth T`. -/
theorem factorial_le_two_pow_depth (T : DecisionTree (Fin n × Fin n) β)
    (hT : DistinguishesPermutations T) :
    Nat.factorial n ≤ 2 ^ DecisionTree.depth T :=
  (factorial_le_leafCount T hT).trans (DecisionTree.leafCount_le_two_pow_depth T)

/-- The worst-case comparison lower bound: the depth of any correct sorting tree
is bounded below by `Nat.clog 2 (n!)`. -/
theorem clog_factorial_le_depth (T : DecisionTree (Fin n × Fin n) β)
    (hT : DistinguishesPermutations T) :
    Nat.clog 2 (Nat.factorial n) ≤ DecisionTree.depth T :=
  Nat.clog_le_of_le_pow (factorial_le_two_pow_depth T hT)

/-! ### Factorial Combinatorial Bounds -/

/-- Combinatorial lower bound on factorial growth: `(n / 2) ^ (n / 2) ≤ n!`. -/
lemma pow_div_two_le_factorial (n : ℕ) : (n / 2) ^ (n / 2) ≤ Nat.factorial n := by
  by_cases hn : n / 2 = 0
  · rw [hn, Nat.pow_zero]
    exact Nat.factorial_pos n
  have hpos : 0 < n / 2 := Nat.pos_of_ne_zero hn
  have h1 : Nat.factorial (n / 2) * (n / 2 + 1) ^ (n - n / 2) ≤
      Nat.factorial (n / 2 + (n - n / 2)) :=
    Nat.factorial_mul_pow_le_factorial
  have h_add : n / 2 + (n - n / 2) = n := Nat.add_sub_of_le (Nat.div_le_self n 2)
  rw [h_add] at h1
  have hbase : n / 2 ≤ n / 2 + 1 := Nat.le_succ _
  have hexp : n / 2 ≤ n - n / 2 := by omega
  have h2 : (n / 2) ^ (n / 2) ≤ (n / 2 + 1) ^ (n - n / 2) := by
    calc (n / 2) ^ (n / 2) ≤ (n / 2) ^ (n - n / 2) := Nat.pow_le_pow_right hpos hexp
    _ ≤ (n / 2 + 1) ^ (n - n / 2) := Nat.pow_le_pow_left hbase _
  have h3 : 1 ≤ Nat.factorial (n / 2) := Nat.factorial_pos (n / 2)
  have h4 : (n / 2 + 1) ^ (n - n / 2) ≤ Nat.factorial (n / 2) * (n / 2 + 1) ^ (n - n / 2) := by
    calc (n / 2 + 1) ^ (n - n / 2) = 1 * (n / 2 + 1) ^ (n - n / 2) := (Nat.one_mul _).symm
    _ ≤ Nat.factorial (n / 2) * (n / 2 + 1) ^ (n - n / 2) := Nat.mul_le_mul_right _ h3
  exact Nat.le_trans h2 (Nat.le_trans h4 h1)

/-- Auxiliary arithmetic bound: for `n ≥ 6`, `n ≤ (n / 2) ^ 2`. -/
lemma nat_div_two_sq_ge (n : ℕ) (hn : 6 ≤ n) : n ≤ (n / 2) ^ 2 := by
  have h3 : 3 ≤ n / 2 := by omega
  have hmod : 2 * (n / 2) + n % 2 = n := Nat.div_add_mod n 2
  have hmod_le : n % 2 ≤ 1 := Nat.le_of_lt_succ (Nat.mod_lt n (by decide))
  have h_bound : 2 * (n / 2) + n % 2 ≤ (n / 2) ^ 2 := by
    calc 2 * (n / 2) + n % 2 ≤ 2 * (n / 2) + 1 := Nat.add_le_add_left hmod_le _
    _ ≤ 2 * (n / 2) + (n / 2) := Nat.add_le_add_left (Nat.le_trans (by decide) h3) _
    _ = 3 * (n / 2) := by omega
    _ ≤ (n / 2) * (n / 2) := Nat.mul_le_mul_right (n / 2) h3
    _ = (n / 2) ^ 2 := by ring
  rwa [hmod] at h_bound

/-- Auxiliary arithmetic bound: for `n ≥ 2`, `n ≤ 3 * (n / 2)`. -/
lemma nat_le_three_mul_div_two (n : ℕ) (hn : 2 ≤ n) : n ≤ 3 * (n / 2) := by
  omega

/-! ### Asymptotic Complexity Bounds -/

/-- Lower asymptotic bound: `n log n` is asymptotically `O(log(n!))` under `Filter.atTop`.
This proves that `log(n!) = Ω(n log n)`. -/
theorem isBigO_n_log_n_factorial :
    (fun n : ℕ ↦ (n : ℝ) * Real.log (n : ℝ)) =O[Filter.atTop]
    (fun n : ℕ ↦ Real.log ((Nat.factorial n : ℕ) : ℝ)) := by
  refine IsBigO.of_bound (6 : ℝ) ?_
  filter_upwards [Filter.eventually_ge_atTop 6] with n hn
  have hn_pos : 0 < (n : ℝ) := by positivity
  have h_half_pos : 0 < ((n / 2 : ℕ) : ℝ) := by
    have : 0 < n / 2 := by omega
    positivity
  have h_log_pos : 0 ≤ Real.log (n : ℝ) := by
    apply Real.log_nonneg
    have : 1 ≤ n := by omega
    exact_mod_cast this
  have h_fact_log_pos : 0 ≤ Real.log ((Nat.factorial n : ℕ) : ℝ) := by
    apply Real.log_nonneg
    have : 1 ≤ Nat.factorial n := Nat.factorial_pos n
    exact_mod_cast this
  simp only [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) h_log_pos),
    abs_of_nonneg h_fact_log_pos]
  have h_n_sq : (n : ℝ) ≤ ((n / 2 : ℕ) : ℝ) ^ 2 := by
    exact_mod_cast nat_div_two_sq_ge n hn
  have h_log_sq : Real.log (n : ℝ) ≤ 2 * Real.log ((n / 2 : ℕ) : ℝ) := by
    calc Real.log (n : ℝ) ≤ Real.log (((n / 2 : ℕ) : ℝ) ^ 2) :=
          Real.log_le_log hn_pos h_n_sq
    _ = 2 * Real.log ((n / 2 : ℕ) : ℝ) := Real.log_pow _ 2
  have h_n_le : (n : ℝ) ≤ 3 * ((n / 2 : ℕ) : ℝ) := by
    exact_mod_cast nat_le_three_mul_div_two n (by omega)
  have h_mul_bound : (n : ℝ) * Real.log (n : ℝ) ≤
      6 * (((n / 2 : ℕ) : ℝ) * Real.log ((n / 2 : ℕ) : ℝ)) := by
    calc (n : ℝ) * Real.log (n : ℝ) ≤
        (3 * ((n / 2 : ℕ) : ℝ)) * (2 * Real.log ((n / 2 : ℕ) : ℝ)) :=
          mul_le_mul h_n_le h_log_sq h_log_pos (by positivity)
    _ = 6 * (((n / 2 : ℕ) : ℝ) * Real.log ((n / 2 : ℕ) : ℝ)) := by ring
  have h_pow_eq : ((n / 2 : ℕ) : ℝ) * Real.log ((n / 2 : ℕ) : ℝ) =
      Real.log (((n / 2 : ℕ) : ℝ) ^ (n / 2 : ℕ)) := (Real.log_pow _ (n / 2)).symm
  rw [h_pow_eq] at h_mul_bound
  have h_comb : ((n / 2 : ℕ) : ℝ) ^ (n / 2 : ℕ) ≤ ((Nat.factorial n : ℕ) : ℝ) := by
    exact_mod_cast pow_div_two_le_factorial n
  have h_pow_pos : 0 < ((n / 2 : ℕ) : ℝ) ^ (n / 2 : ℕ) := by positivity
  have h_log_comb : Real.log (((n / 2 : ℕ) : ℝ) ^ (n / 2 : ℕ)) ≤
      Real.log ((Nat.factorial n : ℕ) : ℝ) :=
    Real.log_le_log h_pow_pos h_comb
  linarith

/-- Upper asymptotic bound: `log(n!)` is asymptotically `O(n log n)` under `Filter.atTop`. -/
theorem isBigO_factorial_n_log_n :
    (fun n : ℕ ↦ Real.log ((Nat.factorial n : ℕ) : ℝ)) =O[Filter.atTop]
    (fun n : ℕ ↦ (n : ℝ) * Real.log (n : ℝ)) := by
  refine IsBigO.of_bound (1 : ℝ) ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hn_pos : 0 < (n : ℝ) := by positivity
  have h_fact_pos : 0 < ((Nat.factorial n : ℕ) : ℝ) := by
    have : 0 < Nat.factorial n := Nat.factorial_pos n
    positivity
  have h_log_n_pos : 0 ≤ Real.log (n : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast hn
  have h_log_fact_pos : 0 ≤ Real.log ((Nat.factorial n : ℕ) : ℝ) := by
    apply Real.log_nonneg
    have : 1 ≤ Nat.factorial n := Nat.factorial_pos n
    exact_mod_cast this
  simp only [Real.norm_eq_abs, abs_of_nonneg h_log_fact_pos,
    abs_of_nonneg (mul_nonneg (by positivity) h_log_n_pos), one_mul]
  have h_pow : (Nat.factorial n : ℝ) ≤ (n : ℝ) ^ n := by
    exact_mod_cast Nat.factorial_le_pow n
  calc Real.log ((Nat.factorial n : ℕ) : ℝ) ≤ Real.log ((n : ℝ) ^ n) :=
        Real.log_le_log h_fact_pos h_pow
  _ = (n : ℝ) * Real.log (n : ℝ) := Real.log_pow (n : ℝ) n

/-- Asymptotic equivalence: `log(n!) = Θ(n log n)` under `Filter.atTop`. -/
theorem isTheta_factorial_n_log_n :
    (fun n : ℕ ↦ Real.log ((Nat.factorial n : ℕ) : ℝ)) =Θ[Filter.atTop]
    (fun n : ℕ ↦ (n : ℝ) * Real.log (n : ℝ)) :=
  ⟨isBigO_factorial_n_log_n, isBigO_n_log_n_factorial⟩

/-- Asymptotic bound connecting `log(n!)` to `Nat.clog 2 (n!)` under `Filter.atTop`. -/
theorem isBigO_log_factorial_clog_factorial :
    (fun n : ℕ ↦ Real.log ((Nat.factorial n : ℕ) : ℝ)) =O[Filter.atTop]
    (fun n : ℕ ↦ ((Nat.clog 2 (Nat.factorial n) : ℕ) : ℝ)) := by
  refine IsBigO.of_bound (1 : ℝ) ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have h_fact_pos : 0 < ((Nat.factorial n : ℕ) : ℝ) := by
    have : 0 < Nat.factorial n := Nat.factorial_pos n
    positivity
  have h_log_fact_pos : 0 ≤ Real.log ((Nat.factorial n : ℕ) : ℝ) := by
    apply Real.log_nonneg
    have : 1 ≤ Nat.factorial n := Nat.factorial_pos n
    exact_mod_cast this
  have h_clog_nonneg : 0 ≤ ((Nat.clog 2 (Nat.factorial n) : ℕ) : ℝ) := by positivity
  simp only [Real.norm_eq_abs, abs_of_nonneg h_log_fact_pos,
    abs_of_nonneg h_clog_nonneg, one_mul]
  have h_pow : Nat.factorial n ≤ 2 ^ Nat.clog 2 (Nat.factorial n) :=
    Nat.le_pow_clog (by decide) (Nat.factorial n)
  have h_log_le : Real.log ((Nat.factorial n : ℕ) : ℝ) ≤
      Real.log (((2 : ℝ)) ^ (Nat.clog 2 (Nat.factorial n))) := by
    apply Real.log_le_log h_fact_pos
    exact_mod_cast h_pow
  rw [Real.log_pow (2 : ℝ)] at h_log_le
  have h_log2_le_one : Real.log (2 : ℝ) ≤ 1 := by
    have h_sub := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 2)
    linarith
  calc Real.log ((Nat.factorial n : ℕ) : ℝ)
    _ ≤ ((Nat.clog 2 (Nat.factorial n) : ℕ) : ℝ) * Real.log 2 := h_log_le
    _ ≤ ((Nat.clog 2 (Nat.factorial n) : ℕ) : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left h_log2_le_one h_clog_nonneg
    _ = ((Nat.clog 2 (Nat.factorial n) : ℕ) : ℝ) := mul_one _

/-- The information-theoretic comparison lower bound: `n log n` is asymptotically
dominated by the decision tree depth bound `Nat.clog 2 (n!)` under `Filter.atTop`. -/
theorem isBigO_n_log_n_clog_factorial :
    (fun n : ℕ ↦ (n : ℝ) * Real.log (n : ℝ)) =O[Filter.atTop]
    (fun n : ℕ ↦ ((Nat.clog 2 (Nat.factorial n) : ℕ) : ℝ)) :=
  isBigO_n_log_n_factorial.trans isBigO_log_factorial_clog_factorial

/-- The asymptotic lower bound on decision tree depth: for any family of decision trees
distinguishing all permutations on `n` elements, `n log n = O(depth(T_n))` under `Filter.atTop`. -/
theorem isBigO_n_log_n_depth {β : (n : ℕ) → Type*}
    (T : (n : ℕ) → DecisionTree (Fin n × Fin n) (β n))
    (hT : ∀ n, DistinguishesPermutations (T n)) :
    (fun n : ℕ ↦ (n : ℝ) * Real.log (n : ℝ)) =O[Filter.atTop]
    (fun n : ℕ ↦ (((T n).depth : ℕ) : ℝ)) := by
  have h_clog_depth : (fun n : ℕ ↦ ((Nat.clog 2 (Nat.factorial n) : ℕ) : ℝ)) =O[Filter.atTop]
      (fun n : ℕ ↦ (((T n).depth : ℕ) : ℝ)) := by
    refine Asymptotics.IsBigO.of_bound (1 : ℝ) ?_
    filter_upwards [Filter.eventually_ge_atTop 0] with n _
    simp only [Real.norm_eq_abs, Nat.abs_cast, one_mul]
    have h := clog_factorial_le_depth (T n) (hT n)
    exact_mod_cast h
  exact isBigO_n_log_n_clog_factorial.trans h_clog_depth

end Amort.Sorting
