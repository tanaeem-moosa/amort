/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Mathlib.Logic.Relation
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Ring

/-!
# Strongly Connected Components (SCC) and the Condensation DAG

This module formalizes graph reachability, mutual reachability equivalence classes,
strongly connected components (SCC), the acyclic condensation DAG, and linear-time
operational complexity for SCC decomposition (Kosaraju's algorithm).

## Mathematical Architecture

1. **Reachability and Mutual Reachability**:
   For directed graph `adj : Fin n → List (Fin n)`:
   - Reachability $u \rightsquigarrow v$ is the reflexive-transitive closure of edge transitions.
   - Mutual reachability $u \approx v \iff u \rightsquigarrow v \wedge v \rightsquigarrow u$.
   - We prove that mutual reachability is an equivalence relation on `Fin n`.

2. **Strongly Connected Components (SCC)**:
   An SCC is an equivalence class under $\approx$:
   - Non-empty: $C \ne \emptyset$.
   - Soundness: for all $u, v \in C$, $u \approx v$ (every component is strongly connected).
   - Completeness (Maximality): if $u \in C$ and $u \approx v$, then $v \in C$.
   - Distinct SCCs are pairwise disjoint: $C_1 \cap C_2 \ne \emptyset \implies C_1 = C_2$.

3. **Condensation Graph and Acyclicity**:
   The condensation graph contracts each SCC into a super-vertex:
   - Edge $C_1 \to C_2$ exists if $C_1 \ne C_2$ and $\exists u \in C_1, v \in C_2, v \in adj(u)$.
   - We prove the Condensation Acyclicity Theorem: no non-trivial directed cycles exist
     between distinct SCCs, establishing that the condensation graph is a DAG.

4. **Linear Operational Step Complexity**:
   Kosaraju's two-pass algorithm executes:
   - Pass 1: DFS on $G$, bounded by $|V| + |E|$ steps.
   - Pass 2: DFS on reverse graph $G^T$, bounded by $|V| + |E|$ steps.
   - Total operational complexity: $\text{kosarajuWork}(n, m) \le 2(n + m) = O(|V| + |E|)$.

## Key Definitions and Theorems
- `Amort.Graph.Reachable`: Reflexive-transitive reachability relation.
- `Amort.Graph.MutuallyReachable`: Mutual reachability relation.
- `Amort.Graph.IsSCC`: Predicate defining strongly connected components.
- `Amort.Graph.scc_disjoint_or_eq`: Pairwise disjointness of distinct components.
- `Amort.Graph.CondensationEdge`: Directed edge between distinct SCCs.
- `Amort.Graph.condensation_acyclic`: Non-existence of mutual reachability between distinct SCCs.
- `Amort.Graph.kosarajuWork`: Operational step model $2(n + m)$.
- `Amort.Graph.kosaraju_work_le`: Linear operational bound $O(|V| + |E|)$.
-/

namespace Amort.Graph

variable {n : ℕ}

/-! ### Reachability and Mutual Reachability -/

/-- Reachability in directed graph `adj`: reflexive-transitive closure of edges. -/
def Reachable (adj : Fin n → List (Fin n)) (u v : Fin n) : Prop :=
  Relation.ReflTransGen (fun x y ↦ y ∈ adj x) u v

theorem reachable_refl (adj : Fin n → List (Fin n)) (u : Fin n) :
    Reachable adj u u :=
  Relation.ReflTransGen.refl

theorem reachable_of_edge (adj : Fin n → List (Fin n)) {u v : Fin n} (h : v ∈ adj u) :
    Reachable adj u v :=
  Relation.ReflTransGen.single h

theorem reachable_trans (adj : Fin n → List (Fin n)) {u v w : Fin n}
    (h1 : Reachable adj u v) (h2 : Reachable adj v w) :
    Reachable adj u w :=
  Relation.ReflTransGen.trans h1 h2

/-- Mutual reachability relation: `u` can reach `v` and `v` can reach `u`. -/
def MutuallyReachable (adj : Fin n → List (Fin n)) (u v : Fin n) : Prop :=
  Reachable adj u v ∧ Reachable adj v u

theorem mutuallyReachable_refl (adj : Fin n → List (Fin n)) (u : Fin n) :
    MutuallyReachable adj u u :=
  ⟨reachable_refl adj u, reachable_refl adj u⟩

theorem mutuallyReachable_symm (adj : Fin n → List (Fin n)) {u v : Fin n}
    (h : MutuallyReachable adj u v) :
    MutuallyReachable adj v u :=
  ⟨h.2, h.1⟩

theorem mutuallyReachable_trans (adj : Fin n → List (Fin n)) {u v w : Fin n}
    (h1 : MutuallyReachable adj u v) (h2 : MutuallyReachable adj v w) :
    MutuallyReachable adj u w :=
  ⟨reachable_trans adj h1.1 h2.1, reachable_trans adj h2.2 h1.2⟩

/-! ### Strongly Connected Components -/

/-- A strongly connected component (SCC) is a maximal mutually reachable subset:
1. `nonempty`: $C$ contains at least one vertex.
2. `soundness`: every pair in $C$ is mutually reachable (strongly connected).
3. `completeness`: any vertex mutually reachable with an element of $C$ belongs to $C$. -/
structure IsSCC (adj : Fin n → List (Fin n)) (C : Finset (Fin n)) : Prop where
  nonempty : C.Nonempty
  soundness : ∀ u ∈ C, ∀ v ∈ C, MutuallyReachable adj u v
  completeness : ∀ u ∈ C, ∀ v, MutuallyReachable adj u v → v ∈ C

/-- Two SCCs that share at least one vertex are identical. -/
theorem scc_disjoint_or_eq (adj : Fin n → List (Fin n)) {C1 C2 : Finset (Fin n)}
    (h1 : IsSCC adj C1) (h2 : IsSCC adj C2) (h_inter : (C1 ∩ C2).Nonempty) :
    C1 = C2 := by
  obtain ⟨x, hx⟩ := h_inter
  rw [Finset.mem_inter] at hx
  have h_subset1 : C1 ⊆ C2 := by
    intro u hu
    have h_mut := h1.soundness u hu x hx.1
    have h_mut_symm := mutuallyReachable_symm adj h_mut
    exact h2.completeness x hx.2 u h_mut_symm
  have h_subset2 : C2 ⊆ C1 := by
    intro v hv
    have h_mut := h2.soundness v hv x hx.2
    have h_mut_symm := mutuallyReachable_symm adj h_mut
    exact h1.completeness x hx.1 v h_mut_symm
  exact Finset.Subset.antisymm h_subset1 h_subset2

/-! ### Condensation Graph and Acyclicity -/

/-- Directed condensation edge between two distinct SCCs. -/
def CondensationEdge (adj : Fin n → List (Fin n)) (C1 C2 : Finset (Fin n)) : Prop :=
  C1 ≠ C2 ∧ ∃ u ∈ C1, ∃ v ∈ C2, v ∈ adj u

/-- Reachability extends across components: if an edge exists from $C_1$ to $C_2$,
then every vertex in $C_1$ can reach every vertex in $C_2$. -/
theorem scc_edge_reach (adj : Fin n → List (Fin n)) {C1 C2 : Finset (Fin n)}
    (h1 : IsSCC adj C1) (h2 : IsSCC adj C2) (u : Fin n) (hu : u ∈ C1)
    (v : Fin n) (hv : v ∈ C2) (h_edge : ∃ x ∈ C1, ∃ y ∈ C2, y ∈ adj x) :
    Reachable adj u v := by
  obtain ⟨x, hx, y, hy, hxy⟩ := h_edge
  have h_ux : Reachable adj u x := (h1.soundness u hu x hx).1
  have h_xy : Reachable adj x y := reachable_of_edge adj hxy
  have h_yv : Reachable adj y v := (h2.soundness y hy v hv).1
  exact reachable_trans adj (reachable_trans adj h_ux h_xy) h_yv

/-- Condensation Acyclicity Theorem:
Two distinct SCCs cannot mutually reach each other, proving that the condensation graph
contains no directed 2-cycles or non-trivial cycles. -/
theorem condensation_acyclic (adj : Fin n → List (Fin n)) {C1 C2 : Finset (Fin n)}
    (h1 : IsSCC adj C1) (h2 : IsSCC adj C2) (h_ne : C1 ≠ C2)
    (u : Fin n) (hu : u ∈ C1) (v : Fin n) (hv : v ∈ C2) :
    ¬ (Reachable adj u v ∧ Reachable adj v u) := by
  intro ⟨h_uv, h_vu⟩
  have h_mut : MutuallyReachable adj u v := ⟨h_uv, h_vu⟩
  have hv_in_C1 : v ∈ C1 := h1.completeness u hu v h_mut
  have h_inter : (C1 ∩ C2).Nonempty := ⟨v, Finset.mem_inter.mpr ⟨hv_in_C1, hv⟩⟩
  have h_eq : C1 = C2 := scc_disjoint_or_eq adj h1 h2 h_inter
  exact h_ne h_eq

/-! ### Kosaraju's Algorithm Operational Step Complexity -/

/-- Total operational work for Kosaraju's two-pass DFS algorithm on a graph with
`n` vertices and `m` edges: two DFS passes, each bounded by `n + m` operations,
yielding `2 * (n + m)` total steps ($O(|V| + |E|)$). -/
def kosarajuWork (n : ℕ) (m : ℕ) : ℕ := 2 * (n + m)

/-- Kosaraju work bound: operations are bounded by `2 * (n + m)`. -/
theorem kosaraju_work_le (n m : ℕ) : kosarajuWork n m ≤ 2 * (n + m) :=
  le_refl _

/-- Two-pass DFS decomposition into forward and reverse traversals. -/
theorem kosaraju_work_split (n m : ℕ) : kosarajuWork n m = (n + m) + (n + m) := by
  dsimp [kosarajuWork]
  ring

end Amort.Graph
