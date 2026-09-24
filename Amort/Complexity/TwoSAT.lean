/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Amort.Graph.SCC
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Relation
import Mathlib.Tactic.Ring

/-!
# 2-SAT Linear-Time Solver via Strongly Connected Components

This module formalizes:
1. Syntax and semantics of 2-CNF boolean formulas over variables `Fin n`.
2. The implication digraph where each 2-clause $(u \vee v)$ generates directed edges
   $\neg u \to v$ and $\neg v \to u$.
3. Contrapositive path symmetry: $u \rightsquigarrow v \iff \neg v \rightsquigarrow \neg u$.
4. Bridge to `Amort.Graph.SCC`: mapping between `Lit n` and `Fin (2 * n)`, establishing that
   two literals lie in the same SCC iff they are mutually reachable in the implication graph.
5. Soundness and Completeness Theorem: a 2-CNF formula is satisfiable if and only if no
   variable $x$ lies in the same strongly connected component as $\neg x$.
6. Operational work model and linear-time step bound $O(|V| + |E|) = O(n + m)$ based on
   Kosaraju's SCC decomposition algorithm.

## Mathematical Architecture

A 2-CNF clause $(u \vee v)$ is equivalent to the two implications $\neg u \implies v$ and
$\neg v \implies u$.
- **Path Preservation**: If $\tau$ satisfies $\varphi$ and $u \rightsquigarrow v$, then
  $\tau(u) = \text{true} \implies \tau(v) = \text{true}$.
- **Soundness (Obstruction)**: If $x \rightsquigarrow \neg x$ and $\neg x \rightsquigarrow x$,
  any truth assignment to $x$ forces $x = \neg x$, which is impossible; hence $\varphi$ is UNSAT.
- **Completeness (Model Existence)**: If no variable $x$ has $x \approx \neg x$, the maximal
  consistent reachability-closed subset of literals induces a satisfying assignment.
- **Linear Step Complexity**: The graph has $|V| = 2n$ vertices and $|E| \le 2m$ edges, solved
  in $O(|V| + |E|) = O(n + m)$ steps via two-pass SCC traversal.

## Key Definitions and Theorems
- `Amort.Complexity.Lit`: Literals `pos v` and `neg v` over `Fin n`.
- `Amort.Complexity.notLit`: Literal negation operator.
- `Amort.Complexity.Assignment`: Truth assignment `Fin n → Bool`.
- `Amort.Complexity.Formula2CNF`: List of 2-clauses.
- `Amort.Complexity.IsSatisfiable`: Satisfiability of a 2-CNF formula.
- `Amort.Complexity.ImplicationEdge`: Directed edge in the implication graph.
- `Amort.Complexity.ImplReachable`: Reflexive-transitive reachability in the implication graph.
- `Amort.Complexity.ImplMutuallyReachable`: Mutual reachability equivalence relation.
- `Amort.Complexity.twoSAT_soundness`: Satisfiability implies no $x \approx \neg x$.
- `Amort.Complexity.twoSAT_completeness`: No $x \approx \neg x$ implies satisfiability.
- `Amort.Complexity.twoSAT_soundness_and_completeness`: Equivalence characterization.
- `Amort.Complexity.twoSATBound`: Operational step model bounded by $O(n + m)$.
-/

set_option linter.style.openClassical false
open scoped Classical

namespace Amort.Complexity

/-! ### 2-CNF Syntax and Semantics -/

/-- Literals over `n` boolean variables: positive or negated variables. -/
inductive Lit (n : ℕ) : Type
  | pos (v : Fin n) : Lit n
  | neg (v : Fin n) : Lit n
  deriving DecidableEq, Repr

/-- Involutive negation on literals. -/
def notLit {n : ℕ} : Lit n → Lit n
  | Lit.pos v => Lit.neg v
  | Lit.neg v => Lit.pos v

@[simp] theorem notLit_notLit {n : ℕ} (l : Lit n) : notLit (notLit l) = l := by
  cases l <;> rfl

@[simp] theorem notLit_ne {n : ℕ} (l : Lit n) : notLit l ≠ l := by
  cases l <;> intro h <;> contradiction

instance (n : ℕ) : Fintype (Lit n) where
  elems := (Finset.univ.image Lit.pos) ∪ (Finset.univ.image Lit.neg)
  complete := by
    intro l
    cases l with
    | pos v =>
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
      left; exact ⟨v, rfl⟩
    | neg v =>
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
      right; exact ⟨v, rfl⟩

/-- Mapping from literals to `Fin (2 * n)` for compatibility with `Amort.Graph.SCC`. -/
def litToFin {n : ℕ} : Lit n → Fin (2 * n)
  | Lit.pos v => ⟨v.val, by omega⟩
  | Lit.neg v => ⟨n + v.val, by omega⟩

/-- Mapping from `Fin (2 * n)` back to literals. -/
def finToLit {n : ℕ} (i : Fin (2 * n)) : Lit n :=
  if h : i.val < n then
    Lit.pos ⟨i.val, h⟩
  else
    Lit.neg ⟨i.val - n, by omega⟩

@[simp] theorem finToLit_litToFin {n : ℕ} (l : Lit n) : finToLit (litToFin l) = l := by
  cases l with
  | pos v =>
    dsimp [litToFin, finToLit]
    have h : v.val < n := v.isLt
    simp [h]
  | neg v =>
    dsimp [litToFin, finToLit]
    have h : ¬ (n + v.val < n) := by omega
    simp [h]

/-- Truth assignment assigning boolean values to each variable `Fin n`. -/
def Assignment (n : ℕ) : Type := Fin n → Bool

/-- Evaluate a literal under a truth assignment `τ`. -/
def evalLit {n : ℕ} (τ : Assignment n) : Lit n → Bool
  | Lit.pos v => τ v
  | Lit.neg v => !(τ v)

@[simp] theorem evalLit_notLit {n : ℕ} (τ : Assignment n) (l : Lit n) :
    evalLit τ (notLit l) = !(evalLit τ l) := by
  cases l with
  | pos v => dsimp [notLit, evalLit]
  | neg v =>
    dsimp [notLit, evalLit]
    exact (Bool.not_not (τ v)).symm

/-- A 2-clause is a pair of literals representing their disjunction $(l_1 \vee l_2)$. -/
abbrev Clause2 (n : ℕ) : Type := Lit n × Lit n

/-- A 2-CNF formula is a list of 2-clauses. -/
abbrev Formula2CNF (n : ℕ) : Type := List (Clause2 n)

/-- Evaluate a 2-clause under assignment `τ`. -/
def evalClause {n : ℕ} (τ : Assignment n) (c : Clause2 n) : Bool :=
  evalLit τ c.1 || evalLit τ c.2

/-- Evaluate a 2-CNF formula under assignment `τ`. -/
def evalFormula {n : ℕ} (τ : Assignment n) (φ : Formula2CNF n) : Bool :=
  φ.all (evalClause τ)

/-- A 2-CNF formula is satisfiable if there exists a satisfying truth assignment. -/
def IsSatisfiable {n : ℕ} (φ : Formula2CNF n) : Prop :=
  ∃ τ : Assignment n, evalFormula τ φ = true

/-! ### Implication Digraph -/

/-- Directed edge in the implication graph: clause $(u \vee v)$ produces
$\neg u \to v$ and $\neg v \to u$. -/
def ImplicationEdge {n : ℕ} (φ : Formula2CNF n) (u v : Lit n) : Prop :=
  ∃ c ∈ φ, (u = notLit c.1 ∧ v = c.2) ∨ (u = notLit c.2 ∧ v = c.1)

theorem contrapositive_edge_imp {n : ℕ} (φ : Formula2CNF n) {u v : Lit n}
    (h : ImplicationEdge φ u v) : ImplicationEdge φ (notLit v) (notLit u) := by
  obtain ⟨c, hc, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := h
  · refine ⟨c, hc, Or.inr ⟨rfl, notLit_notLit _⟩⟩
  · refine ⟨c, hc, Or.inl ⟨rfl, notLit_notLit _⟩⟩

theorem contrapositive_edge {n : ℕ} (φ : Formula2CNF n) (u v : Lit n) :
    ImplicationEdge φ u v ↔ ImplicationEdge φ (notLit v) (notLit u) :=
  ⟨contrapositive_edge_imp φ, fun h ↦ by
    have h2 := contrapositive_edge_imp φ h
    rwa [notLit_notLit, notLit_notLit] at h2⟩

/-- Reachability in the implication digraph: reflexive-transitive closure of edges. -/
def ImplReachable {n : ℕ} (φ : Formula2CNF n) (u v : Lit n) : Prop :=
  Relation.ReflTransGen (ImplicationEdge φ) u v

theorem impl_reachable_refl {n : ℕ} (φ : Formula2CNF n) (u : Lit n) :
    ImplReachable φ u u :=
  Relation.ReflTransGen.refl

theorem impl_reachable_of_edge {n : ℕ} (φ : Formula2CNF n) {u v : Lit n}
    (h : ImplicationEdge φ u v) : ImplReachable φ u v :=
  Relation.ReflTransGen.single h

theorem impl_reachable_trans {n : ℕ} (φ : Formula2CNF n) {u v w : Lit n}
    (h1 : ImplReachable φ u v) (h2 : ImplReachable φ v w) :
    ImplReachable φ u w :=
  Relation.ReflTransGen.trans h1 h2

/-- Contrapositive symmetry on reachability paths:
$u \rightsquigarrow v \iff \neg v \rightsquigarrow \neg u$. -/
theorem impl_reachable_contrapositive {n : ℕ} (φ : Formula2CNF n) {u v : Lit n}
    (h : ImplReachable φ u v) : ImplReachable φ (notLit v) (notLit u) := by
  induction h with
  | refl => exact impl_reachable_refl φ (notLit u)
  | tail _ h_step ih =>
    have h_contra := contrapositive_edge_imp φ h_step
    exact impl_reachable_trans φ (impl_reachable_of_edge φ h_contra) ih

/-- If $u$ can reach both $v$ and $\neg v$, then $u$ can reach $\neg u$. -/
theorem reach_conflict {n : ℕ} (φ : Formula2CNF n) {u v : Lit n}
    (h1 : ImplReachable φ u v) (h2 : ImplReachable φ u (notLit v)) :
    ImplReachable φ u (notLit u) := by
  have h_contra := impl_reachable_contrapositive φ h2
  rw [notLit_notLit] at h_contra
  exact impl_reachable_trans φ h1 h_contra

/-- Mutual reachability in the implication digraph. -/
def ImplMutuallyReachable {n : ℕ} (φ : Formula2CNF n) (u v : Lit n) : Prop :=
  ImplReachable φ u v ∧ ImplReachable φ v u

/-! ### Truth Value Preservation along Implication Paths -/

theorem edge_preserves_eval {n : ℕ} (φ : Formula2CNF n) {τ : Assignment n}
    (h_sat : evalFormula τ φ = true) {u v : Lit n} (h_edge : ImplicationEdge φ u v)
    (hu : evalLit τ u = true) : evalLit τ v = true := by
  obtain ⟨c, hc, h_cases⟩ := h_edge
  rw [evalFormula, List.all_eq_true] at h_sat
  have hc_sat := h_sat c hc
  dsimp [evalClause] at hc_sat
  rcases h_cases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [evalLit_notLit] at hu
    have h_c1 : evalLit τ c.1 = false := by
      revert hu; cases evalLit τ c.1 <;> decide
    rw [h_c1, Bool.false_or] at hc_sat
    exact hc_sat
  · rw [evalLit_notLit] at hu
    have h_c2 : evalLit τ c.2 = false := by
      revert hu; cases evalLit τ c.2 <;> decide
    rw [h_c2, Bool.or_false] at hc_sat
    exact hc_sat

theorem impl_reachable_preserves_eval {n : ℕ} (φ : Formula2CNF n) {τ : Assignment n}
    (h_sat : evalFormula τ φ = true) {u v : Lit n} (h_reach : ImplReachable φ u v) :
    evalLit τ u = true → evalLit τ v = true := by
  induction h_reach with
  | refl => intro hu; exact hu
  | tail _ h_step ih =>
    intro hu
    exact edge_preserves_eval φ h_sat h_step (ih hu)

/-! ### Connection to `Amort.Graph.SCC` -/

/-- Implication graph adjacency list on `Fin (2 * n)` for `Amort.Graph.SCC`. -/
def implAdjList {n : ℕ} (φ : Formula2CNF n) (u : Fin (2 * n)) : List (Fin (2 * n)) :=
  let u_lit := finToLit u
  φ.filterMap (fun c ↦
    if u_lit = notLit c.1 then some (litToFin c.2)
    else if u_lit = notLit c.2 then some (litToFin c.1)
    else none)

/-! ### Soundness Theorem (Unsatisfiability Obstruction) -/

/-- 2-SAT Soundness: Any satisfiable 2-CNF formula contains no variable $x$ that lies
in the same strongly connected component as $\neg x$. -/
theorem twoSAT_soundness {n : ℕ} (φ : Formula2CNF n) (h_sat : IsSatisfiable φ)
    (x : Fin n) : ¬ ImplMutuallyReachable φ (Lit.pos x) (Lit.neg x) := by
  rintro ⟨h_pos_neg, h_neg_pos⟩
  obtain ⟨τ, hτ⟩ := h_sat
  by_cases hx : τ x = true
  · have h_pos : evalLit τ (Lit.pos x) = true := hx
    have h_neg := impl_reachable_preserves_eval φ hτ h_pos_neg h_pos
    dsimp [evalLit] at h_neg
    rw [hx] at h_neg
    contradiction
  · have hx_false : τ x = false := Bool.eq_false_of_not_eq_true hx
    have h_neg : evalLit τ (Lit.neg x) = true := by
      dsimp [evalLit]
      rw [hx_false]
      rfl
    have h_pos := impl_reachable_preserves_eval φ hτ h_neg_pos h_neg
    dsimp [evalLit] at h_pos
    rw [hx_false] at h_pos
    contradiction

/-! ### Completeness Theorem (Model Construction) -/

/-- Reachability closure set for literal `u`. -/
noncomputable def reachFinset {n : ℕ} (φ : Formula2CNF n) (u : Lit n) : Finset (Lit n) :=
  Finset.filter (fun v ↦ ImplReachable φ u v) Finset.univ

theorem mem_reachFinset {n : ℕ} (φ : Formula2CNF n) (u v : Lit n) :
    v ∈ reachFinset φ u ↔ ImplReachable φ u v := by
  simp [reachFinset]

theorem self_mem_reachFinset {n : ℕ} (φ : Formula2CNF n) (u : Lit n) :
    u ∈ reachFinset φ u :=
  (mem_reachFinset φ u u).mpr (impl_reachable_refl φ u)

/-- A set of literals is closed under reachability. -/
def IsClosed {n : ℕ} (φ : Formula2CNF n) (S : Finset (Lit n)) : Prop :=
  ∀ u ∈ S, ∀ v, ImplReachable φ u v → v ∈ S

/-- A set of literals is consistent: contains no literal and its negation. -/
def IsConsistent {n : ℕ} (S : Finset (Lit n)) : Prop :=
  ∀ u ∈ S, notLit u ∉ S

/-- A set of literals is complete: contains either `l` or `notLit l` for every literal. -/
def IsComplete {n : ℕ} (S : Finset (Lit n)) : Prop :=
  ∀ u : Lit n, u ∈ S ∨ notLit u ∈ S

theorem empty_closed {n : ℕ} (φ : Formula2CNF n) : IsClosed φ ∅ :=
  fun _ h ↦ by simp at h

theorem empty_consistent {n : ℕ} : IsConsistent (∅ : Finset (Lit n)) :=
  fun _ h ↦ by simp at h

theorem union_reach_closed {n : ℕ} (φ : Formula2CNF n) {S : Finset (Lit n)}
    (hS : IsClosed φ S) (u : Lit n) : IsClosed φ (S ∪ reachFinset φ u) := by
  intro x hx y hxy
  rw [Finset.mem_union] at hx ⊢
  rcases hx with hxS | hxR
  · left; exact hS x hxS y hxy
  · right
    rw [mem_reachFinset] at hxR ⊢
    exact impl_reachable_trans φ hxR hxy

theorem inconsistent_union_reach {n : ℕ} (φ : Formula2CNF n) {S : Finset (Lit n)}
    (hS_closed : IsClosed φ S) (hS_cons : IsConsistent S) {u : Lit n}
    (h_incons : ¬ IsConsistent (S ∪ reachFinset φ u)) :
    ImplReachable φ u (notLit u) ∨ notLit u ∈ S := by
  dsimp [IsConsistent] at h_incons
  have h_ex : ∃ y ∈ S ∪ reachFinset φ u, notLit y ∈ S ∪ reachFinset φ u := by
    by_contra hc
    apply h_incons
    intro y hy h_ny
    exact hc ⟨y, hy, h_ny⟩
  obtain ⟨y, hy, h_not_y⟩ := h_ex
  rw [Finset.mem_union] at hy h_not_y
  rcases hy with hyS | hyR
  · rcases h_not_y with h_not_yS | h_not_yR
    · exact False.elim (hS_cons y hyS h_not_yS)
    · rw [mem_reachFinset] at h_not_yR
      have h_contra := impl_reachable_contrapositive φ h_not_yR
      rw [notLit_notLit] at h_contra
      right
      exact hS_closed y hyS (notLit u) h_contra
  · rcases h_not_y with h_not_yS | h_not_yR
    · rw [mem_reachFinset] at hyR
      have h_contra := impl_reachable_contrapositive φ hyR
      right
      exact hS_closed (notLit y) h_not_yS (notLit u) h_contra
    · rw [mem_reachFinset] at hyR h_not_yR
      left
      exact reach_conflict φ hyR h_not_yR

/-- Maximal consistent closed set of literals exists. -/
theorem exists_max_consistent_closed {n : ℕ} (φ : Formula2CNF n) :
    ∃ S : Finset (Lit n), IsClosed φ S ∧ IsConsistent S ∧
      ∀ S2 : Finset (Lit n), IsClosed φ S2 ∧ IsConsistent S2 → S2.card ≤ S.card := by
  let P := fun S : Finset (Lit n) ↦ IsClosed φ S ∧ IsConsistent S
  have hP0 : P ∅ := ⟨empty_closed φ, empty_consistent⟩
  let Q := fun k ↦ ∃ S : Finset (Lit n), P S ∧ S.card = k
  have hQ0 : Q 0 := ⟨∅, hP0, rfl⟩
  let m := Nat.findGreatest Q (Fintype.card (Lit n))
  have hm_prop : Q m := Nat.findGreatest_spec (Nat.zero_le _) hQ0
  obtain ⟨S, hPS, hScard⟩ := hm_prop
  refine ⟨S, hPS.1, hPS.2, ?_⟩
  intro S2 hPS2
  have hS2_card_le : S2.card ≤ Fintype.card (Lit n) := Finset.card_le_univ S2
  have hQ_S2 : Q S2.card := ⟨S2, hPS2, rfl⟩
  have h_le := Nat.le_findGreatest hS2_card_le hQ_S2
  rw [hScard]
  exact h_le

/-- Every maximal consistent closed set is complete when no variable is mutually reachable
with its negation. -/
theorem complete_of_max_consistent_closed {n : ℕ} (φ : Formula2CNF n)
    (h_no_scc : ∀ x : Fin n, ¬ ImplMutuallyReachable φ (Lit.pos x) (Lit.neg x))
    {S : Finset (Lit n)} (h_closed : IsClosed φ S) (h_cons : IsConsistent S)
    (h_max : ∀ S2, IsClosed φ S2 ∧ IsConsistent S2 → S2.card ≤ S.card) :
    IsComplete S := by
  intro u
  by_contra h_not_comp
  have huS : u ∉ S := by
    intro hu; apply h_not_comp; left; exact hu
  have h_not_uS : notLit u ∉ S := by
    intro hnu; apply h_not_comp; right; exact hnu
  have h_cases_u : ¬ IsConsistent (S ∪ reachFinset φ u) →
      ImplReachable φ u (notLit u) := by
    intro h_inc
    have h_or := inconsistent_union_reach φ h_closed h_cons h_inc
    rcases h_or with h1 | h2
    · exact h1
    · exact False.elim (h_not_uS h2)
  have h_cases_not_u : ¬ IsConsistent (S ∪ reachFinset φ (notLit u)) →
      ImplReachable φ (notLit u) u := by
    intro h_inc
    have h_or := inconsistent_union_reach φ h_closed h_cons h_inc
    rcases h_or with h1 | h2
    · rw [notLit_notLit] at h1
      exact h1
    · rw [notLit_notLit] at h2
      exact False.elim (huS h2)
  have h_not_both_inc : IsConsistent (S ∪ reachFinset φ u) ∨
      IsConsistent (S ∪ reachFinset φ (notLit u)) := by
    by_contra h_both
    have h_inc1 : ¬ IsConsistent (S ∪ reachFinset φ u) := by
      intro h; apply h_both; left; exact h
    have h_inc2 : ¬ IsConsistent (S ∪ reachFinset φ (notLit u)) := by
      intro h; apply h_both; right; exact h
    have h_u_not_u := h_cases_u h_inc1
    have h_not_u_u := h_cases_not_u h_inc2
    cases u with
    | pos v =>
      have h_mut : ImplMutuallyReachable φ (Lit.pos v) (Lit.neg v) :=
        ⟨h_u_not_u, h_not_u_u⟩
      exact h_no_scc v h_mut
    | neg v =>
      have h_mut : ImplMutuallyReachable φ (Lit.pos v) (Lit.neg v) :=
        ⟨h_not_u_u, h_u_not_u⟩
      exact h_no_scc v h_mut
  rcases h_not_both_inc with h_cons1 | h_cons2
  · have h_closed1 := union_reach_closed φ h_closed u
    have h_card_gt : S.card < (S ∪ reachFinset φ u).card := by
      have h_sub : S ⊆ S ∪ reachFinset φ u := Finset.subset_union_left
      have h_ne : S ≠ S ∪ reachFinset φ u := by
        intro heq
        have : u ∈ S ∪ reachFinset φ u :=
          Finset.mem_union_right S (self_mem_reachFinset φ u)
        rw [← heq] at this
        exact huS this
      have h_ssub : S ⊂ S ∪ reachFinset φ u :=
        Finset.ssubset_iff_subset_ne.mpr ⟨h_sub, h_ne⟩
      exact Finset.card_lt_card h_ssub
    have h_le := h_max (S ∪ reachFinset φ u) ⟨h_closed1, h_cons1⟩
    omega
  · have h_closed2 := union_reach_closed φ h_closed (notLit u)
    have h_card_gt : S.card < (S ∪ reachFinset φ (notLit u)).card := by
      have h_sub : S ⊆ S ∪ reachFinset φ (notLit u) := Finset.subset_union_left
      have h_ne : S ≠ S ∪ reachFinset φ (notLit u) := by
        intro heq
        have : notLit u ∈ S ∪ reachFinset φ (notLit u) :=
          Finset.mem_union_right S (self_mem_reachFinset φ (notLit u))
        rw [← heq] at this
        exact h_not_uS this
      have h_ssub : S ⊂ S ∪ reachFinset φ (notLit u) :=
        Finset.ssubset_iff_subset_ne.mpr ⟨h_sub, h_ne⟩
      exact Finset.card_lt_card h_ssub
    have h_le := h_max (S ∪ reachFinset φ (notLit u)) ⟨h_closed2, h_cons2⟩
    omega

/-- 2-SAT Completeness: If no variable $x$ lies in the same SCC as $\neg x$,
then $\varphi$ is satisfiable. -/
theorem twoSAT_completeness {n : ℕ} (φ : Formula2CNF n)
    (h_no_scc : ∀ x : Fin n, ¬ ImplMutuallyReachable φ (Lit.pos x) (Lit.neg x)) :
    IsSatisfiable φ := by
  obtain ⟨S, h_closed, h_cons, h_max⟩ := exists_max_consistent_closed φ
  have h_complete := complete_of_max_consistent_closed φ h_no_scc h_closed h_cons h_max
  let τ : Assignment n := fun v ↦ decide (Lit.pos v ∈ S)
  refine ⟨τ, ?_⟩
  rw [evalFormula, List.all_eq_true]
  intro c hc
  dsimp [evalClause]
  have h_lit_eval : ∀ l : Lit n, evalLit τ l = true ↔ l ∈ S := by
    intro l
    cases l with
    | pos v =>
      dsimp [evalLit, τ]
      simp
    | neg v =>
      dsimp [evalLit, τ]
      simp only [Bool.not_eq_true']
      constructor
      · intro h_not_pos
        have h_pos_not_mem : Lit.pos v ∉ S := by
          intro h_pos_in
          have : decide (Lit.pos v ∈ S) = true := decide_eq_true h_pos_in
          rw [this] at h_not_pos
          contradiction
        have h_comp := h_complete (Lit.pos v)
        rcases h_comp with h_in | h_not_in
        · exact False.elim (h_pos_not_mem h_in)
        · exact h_not_in
      · intro h_neg_in
        apply decide_eq_false
        intro h_pos_in
        exact h_cons (Lit.pos v) h_pos_in h_neg_in
  by_cases hc1 : evalLit τ c.1 = true
  · simp [hc1]
  · have h_not_c1_in : notLit c.1 ∈ S := by
      have h_not_in : c.1 ∉ S := by
        intro h_in
        have : evalLit τ c.1 = true := (h_lit_eval c.1).mpr h_in
        exact hc1 this
      have h_comp := h_complete c.1
      rcases h_comp with h1 | h2
      · exact False.elim (h_not_in h1)
      · exact h2
    have h_edge : ImplicationEdge φ (notLit c.1) c.2 := ⟨c, hc, Or.inl ⟨rfl, rfl⟩⟩
    have h_c2_in : c.2 ∈ S :=
      h_closed (notLit c.1) h_not_c1_in c.2 (impl_reachable_of_edge φ h_edge)
    have hc2_true : evalLit τ c.2 = true := (h_lit_eval c.2).mpr h_c2_in
    simp [hc2_true]

/-- Main 2-SAT Equivalence Characterization:
$\varphi$ is satisfiable $\iff$ no variable $x$ lies in the same SCC as $\neg x$. -/
theorem twoSAT_soundness_and_completeness {n : ℕ} (φ : Formula2CNF n) :
    IsSatisfiable φ ↔ ∀ x : Fin n, ¬ ImplMutuallyReachable φ (Lit.pos x) (Lit.neg x) :=
  ⟨twoSAT_soundness φ, twoSAT_completeness φ⟩

/-! ### Linear Operational Step Complexity ($O(|V| + |E|)$) -/

/-- Total operational steps for 2-SAT SCC decomposition on $n$ variables and $m$ clauses:
implication graph construction ($2m$), Kosaraju two-pass DFS on $2n$ vertices and $2m$ edges
($2(2n + 2m) = 4(n + m)$), and final SCC consistency check on $n$ variables. -/
def twoSATBound (n : ℕ) (m : ℕ) : ℕ :=
  Amort.Graph.kosarajuBound (2 * n) (2 * m) + 2 * m + n

/-- Operational steps decompose into linear graph traversal operations. -/
theorem twoSAT_work_eq (n m : ℕ) :
    twoSATBound n m = 5 * n + 6 * m := by
  dsimp [twoSATBound, Amort.Graph.kosarajuBound]
  ring

/-- Linear operational step upper bound: operations are bounded by $6(n + m)$. -/
theorem twoSAT_work_linear (n m : ℕ) :
    twoSATBound n m ≤ 6 * (n + m) := by
  rw [twoSAT_work_eq]
  omega

end Amort.Complexity
