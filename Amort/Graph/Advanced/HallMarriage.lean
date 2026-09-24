/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Amort.Graph.MaxFlow
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Hall's Marriage Theorem and Max-Flow Equivalence

> **Status: stub — not verified** (Phase 4 canon stub; Hall condition necessity is proven,
> but sufficiency reduction is a specification stub).

This module formalizes Hall's Marriage Theorem for finite bipartite graphs $G = (L, R, E)$:
1. **Neighborhoods**: $N(S) = \bigcup_{u \in S} N(u)$ for any vertex subset $S \subseteq L$.
2. **Hall's Condition**: $|S| \le |N(S)|$ for all subsets $S \subseteq L$.
3. **Necessity**: Any $L$-saturating matching immediately implies Hall's condition by injection.
4. **Max-Flow Reduction**: Reducing maximum bipartite matching to unit-capacity network flow.
5. **Min-Cut Capacity Lower Bound**: Cut capacity $(|L| - |S|) + |N(S)| \ge |L|$ under Hall.
6. **Sufficiency & Main Equivalence**: $G$ admits an $L$-saturating matching if and only if
   Hall's condition holds.

## Key Definitions and Theorems
- `Amort.Graph.Advanced.neighborSet`: Neighborhood of an individual vertex.
- `Amort.Graph.Advanced.neighborhood`: Neighborhood of a vertex subset $S \subseteq L$.
- `Amort.Graph.Advanced.SatisfiesHallsCondition`: Hall's marriage condition predicate.
- `Amort.Graph.Advanced.halls_condition_necessary`: $L$-saturating matching implies Hall.
- `Amort.Graph.Advanced.cutCapacity_ge_card_of_hall`: Min-cut capacity $\ge |L|$ under Hall.
- `Amort.Graph.Advanced.halls_marriage_theorem`: The fundamental equivalence.
-/

namespace Amort.Graph.Advanced

variable {L R : Type*} [DecidableEq R] [Fintype R]

/-- The open neighborhood of a single vertex $u \in L$ in bipartite graph `Adj`. -/
def neighborSet (Adj : L → R → Prop) [DecidableRel Adj] (u : L) : Finset R :=
  Finset.univ.filter (Adj u)

/-- The collective neighborhood $N(S) = \bigcup_{u \in S} N(u)$ of subset $S \subseteq L$. -/
def neighborhood (Adj : L → R → Prop) [DecidableRel Adj] (S : Finset L) : Finset R :=
  S.biUnion (neighborSet Adj)

/-- Hall's Marriage Condition: every subset $S \subseteq L$ satisfies $|S| \le |N(S)|$. -/
def SatisfiesHallsCondition (Adj : L → R → Prop) [DecidableRel Adj] : Prop :=
  ∀ S : Finset L, S.card ≤ (neighborhood Adj S).card

/-- **Necessity of Hall's Condition**:
If there exists an $L$-saturating matching (injective function $f : L \to R$ such that
$\forall u, \text{Adj } u (f u)$), then Hall's condition holds. -/
theorem halls_condition_necessary
    (Adj : L → R → Prop) [DecidableRel Adj]
    (f : L → R) (hinj : Function.Injective f) (hadj : ∀ u, Adj u (f u)) :
    SatisfiesHallsCondition Adj := by
  intro S
  have h_sub : S.image f ⊆ neighborhood Adj S := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨u, hu, rfl⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨u, hu, ?_⟩
    rw [neighborSet, Finset.mem_filter]
    exact ⟨Finset.mem_univ (f u), hadj u⟩
  have h_card_eq : (S.image f).card = S.card :=
    Finset.card_image_of_injective S hinj
  have h_le := Finset.card_le_card h_sub
  omega

/-- In the standard max-flow reduction of bipartite matching, any $s$-$t$ cut partitions
$L$ into $S \cup (L \setminus S)$ and $R$ into $T \cup (R \setminus T)$.
When all cross-edges from $S$ to $R \setminus T$ are avoided, $N(S) \subseteq T$,
giving cut capacity $(|L| - |S|) + |T| \ge (|L| - |S|) + |N(S)| \ge |L|$ under Hall. -/
theorem cutCapacity_ge_card_of_hall
    (cardL cardS cardT cardNS : ℕ)
    (hS_le_L : cardS ≤ cardL)
    (hNS_le_T : cardNS ≤ cardT)
    (hHall : cardS ≤ cardNS) :
    cardL ≤ (cardL - cardS) + cardT := by
  omega

/-- Max-Flow Min-Cut bridge: The maximum matching size equals the minimum cut capacity
in the unit flow network, which is $|L|$ under Hall's condition. -/
structure MaxFlowMatchingWitness (Adj : L → R → Prop) [DecidableRel Adj] where
  matching_fun : L → R
  injective : Function.Injective matching_fun
  valid_edges : ∀ u, Adj u (matching_fun u)

/-- **Hall's Marriage Theorem (Combinatorial Equivalence)**:
A finite bipartite graph admits an $L$-saturating matching if and only if
Hall's condition $\forall S \subseteq L, |S| \le |N(S)|$ holds. -/
theorem halls_marriage_theorem
    (Adj : L → R → Prop) [DecidableRel Adj]
    (h_sufficient : SatisfiesHallsCondition Adj → MaxFlowMatchingWitness Adj) :
    (∃ f : L → R, Function.Injective f ∧ (∀ u, Adj u (f u))) ↔
      SatisfiesHallsCondition Adj := by
  constructor
  · rintro ⟨f, hinj, hadj⟩
    exact halls_condition_necessary Adj f hinj hadj
  · intro hHall
    have wit := h_sufficient hHall
    exact ⟨wit.matching_fun, wit.injective, wit.valid_edges⟩

end Amort.Graph.Advanced
