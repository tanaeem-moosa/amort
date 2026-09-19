/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Amort.Complexity.Classes
import Amort.Complexity.TwoSAT
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Ring

set_option linter.style.openClassical false
open scoped Classical

/-!
# Karp's Foundational Reductions: 3-SAT, Independent Set, Vertex Cover, and Clique

This module formalizes:
1. Combinatorial graph problem definitions on undirected simple graphs:
   - `IsIndependentSet G S`: Pairwise non-adjacent vertex subset.
   - `IsVertexCover G S`: Subset meeting every edge.
   - `IsClique G S`: Pairwise adjacent vertex subset.
   - Complement graph `complement G`.
2. Complement Duality Theorem:
   In any finite graph $G = (V, E)$ and subset $S \subseteq V$:
   $S$ is an independent set in $G \iff V \setminus S$ is a vertex cover in $G$
   $\iff S$ is a clique in the complement graph $\overline{G}$.
3. 3-SAT syntax and semantics: 3-CNF formulas over variables `Fin n`.
4. 3-SAT to Independent Set reduction using clause triangle gadgets:
   - For each clause $i \in \{0, \dots, m-1\}$, a triangle of 3 vertices $(i, 0), (i, 1), (i, 2)$.
   - Conflict edges between contradictory literals $l_1 = \neg l_2$.
   - Theorem: $\varphi$ is satisfiable $\iff G_\varphi$ contains an independent set of size $m$.
5. Soundness and completeness of reductions:
   3-SAT to Independent Set, Independent Set to Vertex Cover, and Independent Set to Clique.

## Key Definitions and Theorems
- `Amort.Complexity.SimpleGraph`: Undirected simple graph with symmetric, loopless adjacency.
- `Amort.Complexity.SimpleGraph.IsIndependentSet`: Independent set predicate.
- `Amort.Complexity.SimpleGraph.IsVertexCover`: Vertex cover predicate.
- `Amort.Complexity.SimpleGraph.IsClique`: Clique predicate.
- `Amort.Complexity.SimpleGraph.complement`: Complement graph $\overline{G}$.
- `Amort.Complexity.isIndependentSet_iff_isVertexCover_compl`: $S \text{ IS} \iff S^c \text{ VC}$.
- `Amort.Complexity.isIndependentSet_iff_isClique_complement`:
  $S \text{ IS in } G \iff S \text{ Clique in } \overline{G}$.
- `Amort.Complexity.complement_duality`: Tripartite duality theorem.
- `Amort.Complexity.sat3ToISGraph`: Gadget graph construction for 3-SAT.
- `Amort.Complexity.sat3_to_independentSet_soundness`: Satisfiability implies size-$m$ IS.
- `Amort.Complexity.sat3_to_independentSet_completeness`: Size-$m$ IS implies satisfiability.
- `Amort.Complexity.sat3_to_independentSet_correct`: Equivalence theorem.
-/

namespace Amort.Complexity

/-! ### Undirected Simple Graphs -/

/-- An undirected simple graph on vertex type `V`. -/
structure SimpleGraph (V : Type*) where
  Adj : V → V → Prop
  symm : ∀ u v, Adj u v → Adj v u
  loopless : ∀ v, ¬ Adj v v

namespace SimpleGraph

variable {V : Type*}

/-- A subset of vertices `S` is an independent set if no two vertices in `S` are adjacent. -/
def IsIndependentSet (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, ¬ G.Adj u v

/-- A subset of vertices `S` is a vertex cover if every edge has at least one endpoint in `S`. -/
def IsVertexCover (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ u v, G.Adj u v → u ∈ S ∨ v ∈ S

/-- A subset of vertices `S` is a clique if every pair of distinct vertices in `S` are adjacent. -/
def IsClique (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, u ≠ v → G.Adj u v

/-- The complement graph $\overline{G}$: vertices are adjacent in $\overline{G}$ iff they are
distinct and not adjacent in $G$. -/
def complement (G : SimpleGraph V) : SimpleGraph V where
  Adj u v := u ≠ v ∧ ¬ G.Adj u v
  symm := fun _u _v ⟨hne, nadj⟩ ↦ ⟨hne.symm, fun hadj ↦ nadj (G.symm _ _ hadj)⟩
  loopless := fun _v ⟨hne, _⟩ ↦ hne rfl

@[simp] theorem complement_Adj (G : SimpleGraph V) (u v : V) :
    G.complement.Adj u v ↔ u ≠ v ∧ ¬ G.Adj u v :=
  Iff.rfl

end SimpleGraph

/-! ### Complement Duality Theorems -/

/-- Complement Duality Part 1:
A subset $S \subseteq V$ is an independent set in $G$ if and only if its complement $V \setminus S$
is a vertex cover in $G$. -/
theorem isIndependentSet_iff_isVertexCover_compl {V : Type*} [Fintype V]
    (G : SimpleGraph V) (S : Finset V) :
    G.IsIndependentSet S ↔ G.IsVertexCover (Sᶜ) := by
  constructor
  · intro h_ind u v hadj
    by_cases hu : u ∈ Sᶜ
    · exact Or.inl hu
    · by_cases hv : v ∈ Sᶜ
      · exact Or.inr hv
      · have huS : u ∈ S := by
          have : u ∉ Sᶜ := hu
          simpa using this
        have hvS : v ∈ S := by
          have : v ∉ Sᶜ := hv
          simpa using this
        exact (h_ind u huS v hvS hadj).elim
  · intro h_vc u hu v hv hadj
    have h_cov := h_vc u v hadj
    rcases h_cov with hu_compl | hv_compl
    · rw [Finset.mem_compl] at hu_compl
      exact hu_compl hu
    · rw [Finset.mem_compl] at hv_compl
      exact hv_compl hv

/-- Complement Duality Part 2:
A subset $S \subseteq V$ is an independent set in $G$ if and only if $S$ is a clique in the
complement graph $\overline{G}$. -/
theorem isIndependentSet_iff_isClique_complement {V : Type*}
    (G : SimpleGraph V) (S : Finset V) :
    G.IsIndependentSet S ↔ G.complement.IsClique S := by
  constructor
  · intro h_ind u hu v hv hne
    exact ⟨hne, h_ind u hu v hv⟩
  · intro h_clique u hu v hv hadj
    by_cases hne : u = v
    · rw [hne] at hadj
      exact G.loopless v hadj
    · have h_comp := h_clique u hu v hv hne
      exact h_comp.2 hadj

/-- Master Complement Duality Theorem:
In any graph $G = (V, E)$, $S$ is an independent set $\iff V \setminus S$ is a vertex cover
$\iff S$ is a clique in $\overline{G}$. -/
theorem complement_duality {V : Type*} [Fintype V]
    (G : SimpleGraph V) (S : Finset V) :
    (G.IsIndependentSet S ↔ G.IsVertexCover (Sᶜ)) ∧
    (G.IsIndependentSet S ↔ G.complement.IsClique S) ∧
    (G.IsVertexCover (Sᶜ) ↔ G.complement.IsClique S) := by
  have h1 := isIndependentSet_iff_isVertexCover_compl G S
  have h2 := isIndependentSet_iff_isClique_complement G S
  refine ⟨h1, h2, ?_⟩
  rw [← h1]
  exact h2

/-! ### 3-SAT Syntax and Semantics -/

/-- A 3-clause is a triple of literals $(l_1, l_2, l_3)$. -/
abbrev Clause3 (n : ℕ) : Type := Lit n × Lit n × Lit n

/-- A 3-CNF formula is a list of 3-clauses. -/
abbrev Formula3CNF (n : ℕ) : Type := List (Clause3 n)

/-- Evaluate a 3-clause under assignment `τ`. -/
def evalClause3 {n : ℕ} (τ : Assignment n) (c : Clause3 n) : Bool :=
  evalLit τ c.1 || evalLit τ c.2.1 || evalLit τ c.2.2

/-- Evaluate a 3-CNF formula under assignment `τ`. -/
def evalFormula3 {n : ℕ} (τ : Assignment n) (φ : Formula3CNF n) : Bool :=
  φ.all (evalClause3 τ)

/-- Satisfiability of a 3-CNF formula. -/
def IsSatisfiable3 {n : ℕ} (φ : Formula3CNF n) : Prop :=
  ∃ τ : Assignment n, evalFormula3 τ φ = true

/-! ### 3-SAT to Independent Set Gadget Reduction -/

/-- Extract the `j`-th literal ($j \in \{0, 1, 2\}$) from a 3-clause. -/
def getClauseLit {n : ℕ} (c : Clause3 n) : Fin 3 → Lit n
  | ⟨0, _⟩ => c.1
  | ⟨1, _⟩ => c.2.1
  | ⟨2, _⟩ => c.2.2
  | ⟨n + 3, h⟩ => by omega

/-- Construct the gadget graph $G_\varphi$ for formula `φ` with `m` clauses.
Vertex set is `Fin m × Fin 3` ($3m$ vertices).
Edges connect:
1. Vertices within the same clause (forming a triangle $K_3$).
2. Vertices in different clauses carrying contradictory literals ($l_1 = \neg l_2$). -/
def sat3ToISGraph {n m : ℕ} (φ : Formula3CNF n) (h_len : φ.length = m) :
    SimpleGraph (Fin m × Fin 3) where
  Adj u v :=
    let c_u := φ.get ⟨u.1.val, by omega⟩
    let c_v := φ.get ⟨v.1.val, by omega⟩
    let lit_u := getClauseLit c_u u.2
    let lit_v := getClauseLit c_v v.2
    (u.1 = v.1 ∧ u.2 ≠ v.2) ∨ (u.1 ≠ v.1 ∧ lit_u = notLit lit_v)
  symm := by
    rintro ⟨i1, j1⟩ ⟨i2, j2⟩ h
    dsimp at h ⊢
    rcases h with ⟨h_eq, h_ne⟩ | ⟨h_ne, h_lit⟩
    · left
      exact ⟨h_eq.symm, Ne.symm h_ne⟩
    · right
      refine ⟨Ne.symm h_ne, ?_⟩
      rw [h_lit, notLit_notLit]
  loopless := by
    rintro ⟨i, j⟩ h
    dsimp at h
    rcases h with ⟨_, h_ne⟩ | ⟨h_ne, _⟩
    · exact h_ne rfl
    · exact h_ne rfl

/-- Choose a true literal position in a satisfied clause. -/
def pickSatisfiedLit {n : ℕ} (τ : Assignment n) (c : Clause3 n) : Fin 3 :=
  if evalLit τ c.1 = true then ⟨0, by omega⟩
  else if evalLit τ c.2.1 = true then ⟨1, by omega⟩
  else ⟨2, by omega⟩

theorem eval_pickSatisfiedLit {n : ℕ} (τ : Assignment n) (c : Clause3 n)
    (h_sat : evalClause3 τ c = true) :
    evalLit τ (getClauseLit c (pickSatisfiedLit τ c)) = true := by
  dsimp [evalClause3] at h_sat
  dsimp [pickSatisfiedLit]
  by_cases h1 : evalLit τ c.1 = true
  · simp only [h1, ↓reduceIte, getClauseLit]
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    by_cases h2 : evalLit τ c.2.1 = true
    · simp only [h2, ↓reduceIte, getClauseLit]
    · simp only [h2, Bool.false_eq_true, ↓reduceIte, getClauseLit]
      have hc1_false : evalLit τ c.1 = false := Bool.eq_false_of_not_eq_true h1
      have hc2_false : evalLit τ c.2.1 = false := Bool.eq_false_of_not_eq_true h2
      rw [hc1_false, hc2_false] at h_sat
      exact h_sat

/-- Soundness of 3-SAT to Independent Set:
If `φ` is satisfiable, the gadget graph contains an independent set of size $m$. -/
theorem sat3_to_independentSet_soundness {n m : ℕ} (φ : Formula3CNF n)
    (h_len : φ.length = m) (h_sat : IsSatisfiable3 φ) :
    ∃ S : Finset (Fin m × Fin 3),
      (sat3ToISGraph φ h_len).IsIndependentSet S ∧ S.card = m := by
  obtain ⟨τ, hτ⟩ := h_sat
  rw [evalFormula3, List.all_eq_true] at hτ
  let f : Fin m → Fin m × Fin 3 := fun i ↦
    let c := φ.get ⟨i.val, by omega⟩
    (i, pickSatisfiedLit τ c)
  have hf_inj : Function.Injective f := by
    intro i1 i2 h
    dsimp [f] at h
    exact (Prod.mk.inj h).1
  let S : Finset (Fin m × Fin 3) := Finset.univ.image f
  refine ⟨S, ?_, ?_⟩
  · intro u hu v hv hadj
    rw [Finset.mem_image] at hu hv
    obtain ⟨i1, _, rfl⟩ := hu
    obtain ⟨i2, _, rfl⟩ := hv
    dsimp [sat3ToISGraph] at hadj
    rcases hadj with ⟨heq, hne⟩ | ⟨hne, hlit⟩
    · dsimp [f] at heq hne
      have : i1 = i2 := heq
      subst this
      exact hne rfl
    · dsimp [f] at hlit
      let c1 := φ.get ⟨i1.val, by omega⟩
      let c2 := φ.get ⟨i2.val, by omega⟩
      have h1_true : evalLit τ (getClauseLit c1 (pickSatisfiedLit τ c1)) = true :=
        eval_pickSatisfiedLit τ c1 (hτ c1 (List.get_mem φ ⟨i1.val, by omega⟩))
      have h2_true : evalLit τ (getClauseLit c2 (pickSatisfiedLit τ c2)) = true :=
        eval_pickSatisfiedLit τ c2 (hτ c2 (List.get_mem φ ⟨i2.val, by omega⟩))
      have h_not : evalLit τ (getClauseLit c1 (pickSatisfiedLit τ c1)) =
          !(evalLit τ (getClauseLit c2 (pickSatisfiedLit τ c2))) := by
        have h_lit_eq : getClauseLit c1 (pickSatisfiedLit τ c1) =
            notLit (getClauseLit c2 (pickSatisfiedLit τ c2)) := hlit
        rw [h_lit_eq, evalLit_notLit]
      rw [h1_true, h2_true] at h_not
      contradiction
  · rw [Finset.card_image_of_injective Finset.univ hf_inj]
    rw [Finset.card_univ, Fintype.card_fin]

/-- Completeness of 3-SAT to Independent Set:
If the gadget graph contains an independent set of size $m$, `φ` is satisfiable. -/
theorem sat3_to_independentSet_completeness {n m : ℕ} (φ : Formula3CNF n)
    (h_len : φ.length = m)
    (h_indep : ∃ S : Finset (Fin m × Fin 3),
      (sat3ToISGraph φ h_len).IsIndependentSet S ∧ S.card = m) :
    IsSatisfiable3 φ := by
  obtain ⟨S, hS_indep, hS_card⟩ := h_indep
  have h_inj : Set.InjOn Prod.fst (S : Set (Fin m × Fin 3)) := by
    rintro ⟨i1, j1⟩ hu ⟨i2, j2⟩ hv (heq : i1 = i2)
    rw [Finset.mem_coe] at hu hv
    by_contra hne
    have hjne : j1 ≠ j2 := by
      intro heq_j
      have : (i1, j1) = (i2, j2) := Prod.ext heq heq_j
      exact hne this
    have hadj : (sat3ToISGraph φ h_len).Adj (i1, j1) (i2, j2) := by
      dsimp [sat3ToISGraph]
      left
      exact ⟨heq, hjne⟩
    exact hS_indep (i1, j1) hu (i2, j2) hv hadj
  have h_card_image : (S.image Prod.fst).card = m := by
    rw [Finset.card_image_of_injOn h_inj, hS_card]
  have h_image_univ : S.image Prod.fst = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [h_card_image, Fintype.card_fin]
  have h_has_lit : ∀ i : Fin m, ∃ j : Fin 3, (i, j) ∈ S := by
    intro i
    have : i ∈ S.image Prod.fst := by rw [h_image_univ]; exact Finset.mem_univ i
    rw [Finset.mem_image] at this
    obtain ⟨⟨i', j⟩, hj, rfl⟩ := this
    exact ⟨j, hj⟩
  let litOfV : Fin m × Fin 3 → Lit n := fun v ↦
    let c := φ.get ⟨v.1.val, by omega⟩
    getClauseLit c v.2
  have h_no_conflict : ∀ u ∈ S, ∀ v ∈ S, litOfV u ≠ notLit (litOfV v) := by
    rintro ⟨i1, j1⟩ hu ⟨i2, j2⟩ hv h_eq
    by_cases h_same : i1 = i2
    · have heq : (i1, j1) = (i2, j2) := h_inj hu hv h_same
      have h_same_lit : litOfV (i1, j1) = litOfV (i2, j2) := congr_arg litOfV heq
      rw [h_same_lit] at h_eq
      exact notLit_ne (litOfV (i2, j2)) h_eq.symm
    · have hadj : (sat3ToISGraph φ h_len).Adj (i1, j1) (i2, j2) := by
        dsimp [sat3ToISGraph]
        right
        exact ⟨h_same, h_eq⟩
      exact hS_indep (i1, j1) hu (i2, j2) hv hadj
  let litSet : Finset (Lit n) := S.image litOfV
  let τ : Assignment n := fun x ↦ decide (Lit.pos x ∈ litSet)
  refine ⟨τ, ?_⟩
  rw [evalFormula3, List.all_eq_true]
  intro c hc
  obtain ⟨idx, hidx⟩ := List.mem_iff_get.mp hc
  obtain ⟨j, hj⟩ := h_has_lit ⟨idx.val, by omega⟩
  let u : Fin m × Fin 3 := (⟨idx.val, by omega⟩, j)
  have hu_in : u ∈ S := hj
  have h_chosen_in : litOfV u ∈ litSet := Finset.mem_image_of_mem _ hu_in
  have h_eval_chosen : evalLit τ (litOfV u) = true := by
    cases h_chosen : litOfV u with
    | pos x =>
      dsimp [evalLit, τ]
      have : Lit.pos x ∈ litSet := by rwa [h_chosen] at h_chosen_in
      simp [this]
    | neg x =>
      dsimp [evalLit, τ]
      simp only [Bool.not_eq_true']
      apply decide_eq_false
      intro h_pos_in
      rw [Finset.mem_image] at h_pos_in
      obtain ⟨v, hv, hv_lit⟩ := h_pos_in
      have h_contra := h_no_conflict v hv u hu_in
      rw [hv_lit, h_chosen] at h_contra
      exact h_contra rfl
  have hc_eq : c = φ.get ⟨idx.val, by omega⟩ := by
    have : ⟨idx.val, by omega⟩ = idx := by ext; rfl
    rw [this, hidx]
  rw [hc_eq]
  have hj_cases : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 := by
    have hj_lt := j.isLt
    omega
  have h_idx_eq : (⟨idx.val, by omega⟩ : Fin φ.length) = idx := rfl
  rcases hj_cases with hj0 | hj1 | hj2
  · have hj_eq : j = ⟨0, by omega⟩ := Fin.ext hj0
    have h_eval1 : evalLit τ (φ.get ⟨idx.val, by omega⟩).1 = true := by
      have : litOfV u = getClauseLit (φ.get ⟨idx.val, by omega⟩) j := rfl
      rw [this, hj_eq] at h_eval_chosen
      exact h_eval_chosen
    dsimp [evalClause3]
    rw [h_idx_eq] at h_eval1
    change (evalLit τ (φ.get idx).1 ||
      evalLit τ (φ.get idx).2.1 || evalLit τ (φ.get idx).2.2) = true
    rw [h_eval1, Bool.true_or, Bool.true_or]
  · have hj_eq : j = ⟨1, by omega⟩ := Fin.ext hj1
    have h_eval2 : evalLit τ (φ.get ⟨idx.val, by omega⟩).2.1 = true := by
      have : litOfV u = getClauseLit (φ.get ⟨idx.val, by omega⟩) j := rfl
      rw [this, hj_eq] at h_eval_chosen
      exact h_eval_chosen
    dsimp [evalClause3]
    rw [h_idx_eq] at h_eval2
    change (evalLit τ (φ.get idx).1 ||
      evalLit τ (φ.get idx).2.1 || evalLit τ (φ.get idx).2.2) = true
    rw [h_eval2, Bool.or_true, Bool.true_or]
  · have hj_eq : j = ⟨2, by omega⟩ := Fin.ext hj2
    have h_eval3 : evalLit τ (φ.get ⟨idx.val, by omega⟩).2.2 = true := by
      have : litOfV u = getClauseLit (φ.get ⟨idx.val, by omega⟩) j := rfl
      rw [this, hj_eq] at h_eval_chosen
      exact h_eval_chosen
    dsimp [evalClause3]
    rw [h_idx_eq] at h_eval3
    change (evalLit τ (φ.get idx).1 ||
      evalLit τ (φ.get idx).2.1 || evalLit τ (φ.get idx).2.2) = true
    rw [h_eval3, Bool.or_true]

/-- Main 3-SAT to Independent Set Theorem:
Formula $\varphi$ is satisfiable if and only if the gadget graph $G_\varphi$
has an independent set of size $m$. -/
theorem sat3_to_independentSet_correct {n m : ℕ} (φ : Formula3CNF n)
    (h_len : φ.length = m) :
    IsSatisfiable3 φ ↔
      ∃ S : Finset (Fin m × Fin 3),
        (sat3ToISGraph φ h_len).IsIndependentSet S ∧ S.card = m :=
  ⟨sat3_to_independentSet_soundness φ h_len,
   sat3_to_independentSet_completeness φ h_len⟩

/-! ### Reduction Chain: 3-SAT ≤P Independent Set ≤P Vertex Cover ≤P Clique -/

/-- Independent Set to Vertex Cover problem equivalence:
$(G, k) \in \text{IS} \iff (G, |V| - k) \in \text{VC}$. -/
theorem independentSet_to_vertexCover_iff {V : Type*} [Fintype V]
    (G : SimpleGraph V) (k : ℕ) (hk : k ≤ Fintype.card V) :
    (∃ S : Finset V, G.IsIndependentSet S ∧ S.card = k) ↔
    (∃ C : Finset V, G.IsVertexCover C ∧ C.card = Fintype.card V - k) := by
  constructor
  · rintro ⟨S, h_ind, rfl⟩
    refine ⟨Sᶜ, (isIndependentSet_iff_isVertexCover_compl G S).mp h_ind, ?_⟩
    rw [Finset.card_compl]
  · rintro ⟨C, h_vc, h_card⟩
    refine ⟨Cᶜ, (isIndependentSet_iff_isVertexCover_compl G (Cᶜ)).mpr ?_, ?_⟩
    · rwa [compl_compl]
    · rw [Finset.card_compl, h_card]
      omega

/-- Independent Set to Clique problem equivalence:
$(G, k) \in \text{IS} \iff (\overline{G}, k) \in \text{Clique}$. -/
theorem independentSet_to_clique_iff {V : Type*}
    (G : SimpleGraph V) (k : ℕ) :
    (∃ S : Finset V, G.IsIndependentSet S ∧ S.card = k) ↔
    (∃ K : Finset V, G.complement.IsClique K ∧ K.card = k) := by
  constructor
  · rintro ⟨S, h_ind, h_card⟩
    exact ⟨S, (isIndependentSet_iff_isClique_complement G S).mp h_ind, h_card⟩
  · rintro ⟨K, h_clique, h_card⟩
    exact ⟨K, (isIndependentSet_iff_isClique_complement G K).mpr h_clique, h_card⟩

/-- Vertex Cover to Clique problem equivalence:
$(G, |V| - k) \in \text{VC} \iff (\overline{G}, k) \in \text{Clique}$. -/
theorem vertexCover_to_clique_iff {V : Type*} [Fintype V]
    (G : SimpleGraph V) (k : ℕ) (hk : k ≤ Fintype.card V) :
    (∃ C : Finset V, G.IsVertexCover C ∧ C.card = Fintype.card V - k) ↔
    (∃ K : Finset V, G.complement.IsClique K ∧ K.card = k) := by
  rw [← independentSet_to_vertexCover_iff G k hk]
  exact independentSet_to_clique_iff G k

end Amort.Complexity
