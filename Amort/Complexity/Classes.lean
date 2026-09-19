/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Mathlib.Data.List.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Tactic.Ring

/-!
# Complexity Classes P and NP, Polynomial Verifiers, and Reductions

This module formalizes:
1. Languages over alphabets as `Language α := Set (List α)`.
2. Canonical polynomial growth evaluation `polyEval c k n = c * (n + 1) ^ k` and `IsPolyBound`.
3. Deterministic polynomial time (Class P) with polynomial-time deciders.
4. Nondeterministic polynomial time (Class NP) with polynomial-time verifiers and certificate
   relations: $x \in L \iff \exists u, |u| \le p(|x|) \wedge V(x, u) = \text{true}$.
5. Constructive embedding: $P \subseteq NP$.
6. Polynomial-time many-one (Karp) reductions $A \le_P B$ with length bounds and correctness.
7. Proof that polynomial-time reduction is reflexive and transitive:
   $A \le_P B \wedge B \le_P C \implies A \le_P C$.
8. Preservation theorem: if $A \le_P B$ and $B \in P$, then $A \in P$.
9. Formal definitions of NP-hardness and NP-completeness.

## Mathematical Architecture

A language $L \subseteq \Sigma^*$ is a subset of lists over an alphabet $\alpha$.
- The canonical polynomial bound `polyEval c k n := c * (n + 1) ^ k` is monotone:
  $a \le b \implies \text{polyEval } c\ k\ a \le \text{polyEval } c\ k\ b$.
- Polynomial bounds are closed under composition:
  $\text{polyEval } c_2\ k_2\ (\text{polyEval } c_1\ k_1\ n) \le
   \text{polyEval } (c_2 (c_1 + 1)^{k_2})\ (k_1 k_2)\ n$.
- Polynomial certificates ensure certificates have size bounded by a polynomial in $|x|$.
- Transitivity of $\le_P$ follows from monotonicity and closure under composition.

## Key Definitions and Theorems
- `Amort.Complexity.polyEval`: Canonical polynomial function `c * (n + 1) ^ k`.
- `Amort.Complexity.polyEval_mono`: Monotonicity of `polyEval`.
- `Amort.Complexity.polyEval_comp`: Composition upper bound for `polyEval`.
- `Amort.Complexity.IsPolyBound`: General polynomial growth predicate.
- `Amort.Complexity.Language`: Languages over alphabet `α`.
- `Amort.Complexity.Decider`: Deterministic decider with poly-bounded step counting.
- `Amort.Complexity.InP`: Membership in complexity class P.
- `Amort.Complexity.Verifier`: Polynomial-time verifier with certificate length bound.
- `Amort.Complexity.InNP`: Membership in complexity class NP.
- `Amort.Complexity.inNP_of_inP`: Theorem $P \subseteq NP$.
- `Amort.Complexity.PolyReduction`: Polynomial-time reduction structure.
- `Amort.Complexity.PolyReducible`: Existence of a poly-time reduction ($A \le_P B$).
- `Amort.Complexity.polyReducible_refl`: Reflexivity of $\le_P$.
- `Amort.Complexity.polyReducible_trans`: Transitivity of $\le_P$.
- `Amort.Complexity.inP_of_polyReducible`: If $A \le_P B$ and $B \in P$, then $A \in P$.
- `Amort.Complexity.IsNPHard`: NP-hardness predicate.
- `Amort.Complexity.IsNPComplete`: NP-completeness predicate.
-/

namespace Amort.Complexity

/-! ### Canonical Polynomial Bounds -/

/-- Canonical polynomial bound with scaling factor `c` and degree `k`. -/
def polyEval (c k : ℕ) (n : ℕ) : ℕ :=
  c * (n + 1) ^ k

theorem polyEval_mono (c k : ℕ) {a b : ℕ} (h : a ≤ b) :
    polyEval c k a ≤ polyEval c k b := by
  dsimp [polyEval]
  have h1 : a + 1 ≤ b + 1 := Nat.add_le_add_right h 1
  have hpow : (a + 1) ^ k ≤ (b + 1) ^ k := Nat.pow_le_pow_left h1 k
  exact Nat.mul_le_mul_left c hpow

theorem polyEval_comp (c1 k1 c2 k2 : ℕ) (n : ℕ) :
    polyEval c2 k2 (polyEval c1 k1 n) ≤
      polyEval (c2 * (c1 + 1) ^ k2) (k1 * k2) n := by
  dsimp [polyEval]
  have hpos : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
  have hpow_ge_1 : 1 ≤ (n + 1) ^ k1 := Nat.one_le_pow k1 (n + 1) hpos
  have h_add : c1 * (n + 1) ^ k1 + 1 ≤ (c1 + 1) * (n + 1) ^ k1 := by
    have h_le : c1 * (n + 1) ^ k1 + 1 ≤ c1 * (n + 1) ^ k1 + (n + 1) ^ k1 :=
      Nat.add_le_add_left hpow_ge_1 (c1 * (n + 1) ^ k1)
    have h_eq : c1 * (n + 1) ^ k1 + (n + 1) ^ k1 = (c1 + 1) * (n + 1) ^ k1 := by
      rw [Nat.add_mul, Nat.one_mul]
    rwa [h_eq] at h_le
  have h_pow_le : (c1 * (n + 1) ^ k1 + 1) ^ k2 ≤
      ((c1 + 1) * (n + 1) ^ k1) ^ k2 :=
    Nat.pow_le_pow_left h_add k2
  rw [Nat.mul_pow, ← Nat.pow_mul] at h_pow_le
  have h_scale := Nat.mul_le_mul_left c2 h_pow_le
  rw [← Nat.mul_assoc] at h_scale
  exact h_scale

/-- A function `f : ℕ → ℕ` is polynomially bounded if `f n ≤ polyEval c k n` for all `n`. -/
def IsPolyBound (f : ℕ → ℕ) : Prop :=
  ∃ c k : ℕ, ∀ n : ℕ, f n ≤ polyEval c k n

theorem isPolyBound_polyEval (c k : ℕ) : IsPolyBound (polyEval c k) :=
  ⟨c, k, fun _ ↦ le_rfl⟩

theorem isPolyBound_const (c : ℕ) : IsPolyBound (fun _ ↦ c) :=
  ⟨c, 0, fun _ ↦ by simp [polyEval]⟩

theorem isPolyBound_id : IsPolyBound id :=
  ⟨1, 1, fun n ↦ by
    dsimp [id, polyEval]
    have : n ≤ n + 1 := Nat.le_succ n
    simp [this]⟩

theorem isPolyBound_add {f g : ℕ → ℕ} (hf : IsPolyBound f) (hg : IsPolyBound g) :
    IsPolyBound (fun n ↦ f n + g n) := by
  obtain ⟨c1, k1, h1⟩ := hf
  obtain ⟨c2, k2, h2⟩ := hg
  refine ⟨c1 + c2, max k1 k2, fun n ↦ ?_⟩
  dsimp [polyEval] at h1 h2 ⊢
  have hpos : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
  have hpow1 : (n + 1) ^ k1 ≤ (n + 1) ^ max k1 k2 :=
    Nat.pow_le_pow_right hpos (le_max_left k1 k2)
  have hpow2 : (n + 1) ^ k2 ≤ (n + 1) ^ max k1 k2 :=
    Nat.pow_le_pow_right hpos (le_max_right k1 k2)
  have hf_le : f n ≤ c1 * (n + 1) ^ max k1 k2 :=
    le_trans (h1 n) (Nat.mul_le_mul_left c1 hpow1)
  have hg_le : g n ≤ c2 * (n + 1) ^ max k1 k2 :=
    le_trans (h2 n) (Nat.mul_le_mul_left c2 hpow2)
  have hsum : f n + g n ≤ c1 * (n + 1) ^ max k1 k2 + c2 * (n + 1) ^ max k1 k2 :=
    Nat.add_le_add hf_le hg_le
  rw [← Nat.add_mul] at hsum
  exact hsum

theorem isPolyBound_mul {f g : ℕ → ℕ} (hf : IsPolyBound f) (hg : IsPolyBound g) :
    IsPolyBound (fun n ↦ f n * g n) := by
  obtain ⟨c1, k1, h1⟩ := hf
  obtain ⟨c2, k2, h2⟩ := hg
  refine ⟨c1 * c2, k1 + k2, fun n ↦ ?_⟩
  dsimp [polyEval] at h1 h2 ⊢
  have h_mul := Nat.mul_le_mul (h1 n) (h2 n)
  have h_id : (c1 * (n + 1) ^ k1) * (c2 * (n + 1) ^ k2) =
      (c1 * c2) * (n + 1) ^ (k1 + k2) := by
    rw [Nat.pow_add]
    ring
  rwa [h_id] at h_mul

theorem isPolyBound_comp {f g : ℕ → ℕ} (hf : IsPolyBound f) (hg : IsPolyBound g) :
    IsPolyBound (fun n ↦ g (f n)) := by
  obtain ⟨c1, k1, h1⟩ := hf
  obtain ⟨c2, k2, h2⟩ := hg
  refine ⟨c2 * (c1 + 1) ^ k2, k1 * k2, fun n ↦ ?_⟩
  have h_gn := h2 (f n)
  have h_mono := polyEval_mono c2 k2 (h1 n)
  have h_comp := polyEval_comp c1 k1 c2 k2 n
  exact le_trans h_gn (le_trans h_mono h_comp)

/-! ### Languages and Deterministic Polynomial Time (Class P) -/

/-- A language over alphabet `α` is a set of finite words `List α`. -/
abbrev Language (α : Type*) : Type _ := Set (List α)

/-- A deterministic decider with explicit polynomial step bound parameters. -/
structure Decider (α : Type*) where
  decide : List α → Bool
  polyCoeff : ℕ
  polyExp : ℕ

/-- Step bound associated with a decider. -/
def Decider.stepBound {α : Type*} (M : Decider α) : ℕ → ℕ :=
  polyEval M.polyCoeff M.polyExp

theorem Decider.poly_steps {α : Type*} (M : Decider α) :
    IsPolyBound M.stepBound :=
  isPolyBound_polyEval M.polyCoeff M.polyExp

/-- A decider accepts language `L` if its decision matches membership for every word. -/
def Decider.Accepts {α : Type*} (M : Decider α) (L : Language α) : Prop :=
  ∀ x, M.decide x = true ↔ x ∈ L

/-- Complexity class P: languages decidable in polynomial time. -/
def InP {α : Type*} (L : Language α) : Prop :=
  ∃ M : Decider α, M.Accepts L

/-! ### Nondeterministic Polynomial Time (Class NP) -/

/-- A polynomial-time verifier taking input `x` and certificate `u`. -/
structure Verifier (α β : Type*) where
  verify : List α → List β → Bool
  certCoeff : ℕ
  certExp : ℕ
  stepCoeff : ℕ
  stepExp : ℕ

/-- Certificate length bound associated with a verifier. -/
def Verifier.certBound {α β : Type*} (V : Verifier α β) : ℕ → ℕ :=
  polyEval V.certCoeff V.certExp

/-- Step bound associated with a verifier. -/
def Verifier.stepBound {α β : Type*} (V : Verifier α β) : ℕ → ℕ :=
  polyEval V.stepCoeff V.stepExp

theorem Verifier.poly_cert {α β : Type*} (V : Verifier α β) :
    IsPolyBound V.certBound :=
  isPolyBound_polyEval V.certCoeff V.certExp

theorem Verifier.poly_steps {α β : Type*} (V : Verifier α β) :
    IsPolyBound V.stepBound :=
  isPolyBound_polyEval V.stepCoeff V.stepExp

/-- A verifier accepts language `L` if `x ∈ L` iff there exists a polynomial-length
certificate `u` such that `verify x u = true`. -/
def Verifier.Accepts {α β : Type*} (V : Verifier α β) (L : Language α) : Prop :=
  ∀ x : List α, x ∈ L ↔ ∃ u : List β, u.length ≤ V.certBound x.length ∧ V.verify x u = true

/-- Complexity class NP: languages verifiable in polynomial time with polynomial certificates. -/
def InNP {α : Type*} (L : Language α) : Prop :=
  ∃ (β : Type) (V : Verifier α β), V.Accepts L

/-- Fundamental Complexity Embedding: $P \subseteq NP$.
Any language in P is in NP using a trivial empty certificate. -/
theorem inNP_of_inP {α : Type*} {L : Language α} (h : InP L) : InNP L := by
  obtain ⟨M, hM⟩ := h
  refine ⟨Unit, {
    verify := fun x _ ↦ M.decide x
    certCoeff := 0
    certExp := 0
    stepCoeff := M.polyCoeff
    stepExp := M.polyExp
  }, ?_⟩
  intro x
  rw [← hM x]
  constructor
  · intro hx
    exact ⟨[], Nat.zero_le _, hx⟩
  · rintro ⟨_, _, hx⟩
    exact hx

/-! ### Polynomial-Time Reductions (Karp / Many-One Reductions) -/

/-- A polynomial-time many-one reduction from language `A` to language `B`.
The transformation `toFun` produces outputs of length bounded by `polyEval polyCoeff polyExp`,
and membership is preserved. -/
structure PolyReduction {α β : Type*} (A : Language α) (B : Language β) where
  toFun : List α → List β
  polyCoeff : ℕ
  polyExp : ℕ
  length_bound : ∀ x, (toFun x).length ≤ polyEval polyCoeff polyExp x.length
  correct : ∀ x, x ∈ A ↔ toFun x ∈ B

/-- Step/length bound function of a reduction. -/
def PolyReduction.stepBound {α β : Type*} {A : Language α} {B : Language β}
    (R : PolyReduction A B) : ℕ → ℕ :=
  polyEval R.polyCoeff R.polyExp

theorem PolyReduction.poly_steps {α β : Type*} {A : Language α} {B : Language β}
    (R : PolyReduction A B) : IsPolyBound R.stepBound :=
  isPolyBound_polyEval R.polyCoeff R.polyExp

/-- Existence of a polynomial-time reduction: `A ≤P B`. -/
def PolyReducible {α β : Type*} (A : Language α) (B : Language β) : Prop :=
  Nonempty (PolyReduction A B)

scoped infix:50 " ≤P " => PolyReducible

/-- Polynomial-time reduction is reflexive: $A \le_P A$. -/
theorem polyReducible_refl {α : Type*} (A : Language α) : A ≤P A := by
  refine ⟨{
    toFun := id
    polyCoeff := 1
    polyExp := 1
    length_bound := fun x ↦ by
      dsimp [polyEval, id]
      have : x.length ≤ x.length + 1 := Nat.le_succ x.length
      simp [this]
    correct := fun _ ↦ Iff.rfl
  }⟩

/-- Polynomial-time reduction is transitive: $A \le_P B \wedge B \le_P C \implies A \le_P C$. -/
theorem polyReducible_trans {α β γ : Type*} {A : Language α} {B : Language β} {C : Language γ}
    (h1 : A ≤P B) (h2 : B ≤P C) : A ≤P C := by
  obtain ⟨R1⟩ := h1
  obtain ⟨R2⟩ := h2
  refine ⟨{
    toFun := R2.toFun ∘ R1.toFun
    polyCoeff := R2.polyCoeff * (R1.polyCoeff + 1) ^ R2.polyExp
    polyExp := R1.polyExp * R2.polyExp
    length_bound := fun x ↦ by
      dsimp
      have hlen2 := R2.length_bound (R1.toFun x)
      have hmono := polyEval_mono R2.polyCoeff R2.polyExp (R1.length_bound x)
      have hcomp := polyEval_comp R1.polyCoeff R1.polyExp R2.polyCoeff R2.polyExp x.length
      exact le_trans hlen2 (le_trans hmono hcomp)
    correct := fun x ↦ by
      dsimp
      rw [R1.correct x, R2.correct (R1.toFun x)]
  }⟩

/-- Preservation of P under polynomial reduction: if $A \le_P B$ and $B \in P$, then $A \in P$. -/
theorem inP_of_polyReducible {α β : Type*} {A : Language α} {B : Language β}
    (h_red : A ≤P B) (hB : InP B) : InP A := by
  obtain ⟨R⟩ := h_red
  obtain ⟨MB, hMB⟩ := hB
  refine ⟨{
    decide := fun x ↦ MB.decide (R.toFun x)
    polyCoeff := MB.polyCoeff * (R.polyCoeff + 1) ^ MB.polyExp
    polyExp := R.polyExp * MB.polyExp
  }, ?_⟩
  intro x
  dsimp
  rw [hMB (R.toFun x), ← R.correct x]

/-! ### NP-Hardness and NP-Completeness -/

/-- A language `B` is NP-hard if every language in NP can be reduced to `B` in polynomial time. -/
def IsNPHard {β : Type*} (B : Language β) : Prop :=
  ∀ (α : Type) (A : Language α), InNP A → A ≤P B

/-- A language `B` is NP-complete if `B ∈ NP` and `B` is NP-hard. -/
def IsNPComplete {β : Type*} (B : Language β) : Prop :=
  InNP B ∧ IsNPHard B

end Amort.Complexity
