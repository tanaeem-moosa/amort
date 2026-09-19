# Computational Complexity, NP-Completeness, and Reductions in Lean 4

## Executive Summary

The `Amort.Complexity` module formalizes computational complexity classes, 2-SAT linear-time SCC solving,
and Karp's foundational reduction chain in Lean 4.

The module is structured into four core Lean files:
1. `Amort/Complexity/Classes.lean`: Complexity classes P and NP, verifiers, polynomial certificates,
   polynomial-time many-one (Karp) reductions, transitivity, and NP-completeness.
2. `Amort/Complexity/TwoSAT.lean`: 2-CNF boolean logic, implication digraph, connection to
   `Amort.Graph.SCC`, soundness & completeness characterization ($x \approx \neg x$), and $O(n + m)$ linear time.
3. `Amort/Complexity/KarpReductions.lean`: 3-SAT, Independent Set, Vertex Cover, Clique,
   Complement Duality Theorem, clause triangle gadget reduction soundness/completeness, and reduction chain.
4. `Amort/Complexity/Asymptotics.lean`: Mathlib `Mathlib.Analysis.Asymptotics.IsBigO` bridges for
   2-SAT linear time, canonical polynomial growth, and reduction gadget size bounds.

---

## Architectural Map

```
                          ┌───────────────────────────┐
                          │   Complexity Classes      │
                          │   P, NP, P ⊆ NP, ≤_P      │
                          │   (Classes.lean)          │
                          └─────────────┬─────────────┘
                                        │
           ┌────────────────────────────┼────────────────────────────┐
           ▼                                                         ▼
┌───────────────────────────┐                             ┌───────────────────────────┐
│   2-SAT Linear Solver     │                             │   Karp's Reductions       │
│   Implication Graph & SCC │                             │   3-SAT ≤P IS ≤P VC ≤P CL │
│   (TwoSAT.lean)           │                             │   (KarpReductions.lean)   │
└──────────┬────────────────┘                             └──────────┬────────────────┘
           │                                                         │
           └────────────────────────────┬────────────────────────────┘
                                        ▼
                          ┌───────────────────────────┐
                          │   Mathlib Asymptotics     │
                          │   IsBigO under atTop      │
                          │   (Asymptotics.lean)      │
                          └───────────────────────────┘
```

---

## Complete Theorem Index

### Track 1: Classes P and NP (`Amort.Complexity.Classes`)
- `polyEval_mono`: Monotonicity of canonical polynomial evaluation.
- `polyEval_comp`: Composition inequality for polynomial bounds.
- `isPolyBound_add`, `isPolyBound_mul`, `isPolyBound_comp`: Algebraic closure of polynomial growth.
- `inNP_of_inP`: Constructive embedding $P \subseteq NP$.
- `polyReducible_refl`: Reflexivity of polynomial reduction ($A \le_P A$).
- `polyReducible_trans`: Transitivity of polynomial reduction ($A \le_P B \wedge B \le_P C \implies A \le_P C$).
- `inP_of_polyReducible`: Preservation of Class P under reduction.

### Track 2: 2-SAT Linear Solver via SCC (`Amort.Complexity.TwoSAT`)
- `contrapositive_edge`: Single-step implication symmetry $u \to v \iff \neg v \to \neg u$.
- `impl_reachable_contrapositive`: Path contrapositive symmetry $u \rightsquigarrow v \iff \neg v \rightsquigarrow \neg u$.
- `reach_conflict`: $u \rightsquigarrow v \wedge u \rightsquigarrow \neg v \implies u \rightsquigarrow \neg u$.
- `edge_preserves_eval`, `impl_reachable_preserves_eval`: Truth preservation along implication paths.
- `twoSAT_soundness`: Satisfiable $\implies \forall x, \neg(x \approx \neg x)$.
- `twoSAT_completeness`: $\forall x, \neg(x \approx \neg x) \implies$ Satisfiable.
- `twoSAT_soundness_and_completeness`: Equivalence characterization theorem.
- `twoSAT_work_linear`: Operational steps bounded by $6(n + m)$.

### Track 3: Karp's Reductions & Complement Duality (`Amort.Complexity.KarpReductions`)
- `isIndependentSet_iff_isVertexCover_compl`: $S \text{ IS in } G \iff S^c \text{ VC in } G$.
- `isIndependentSet_iff_isClique_complement`: $S \text{ IS in } G \iff S \text{ Clique in } \overline{G}$.
- `complement_duality`: Tripartite equivalence between IS, VC, and Clique.
- `sat3_to_independentSet_soundness`: $\varphi \in \text{3-SAT} \implies G_\varphi$ has IS of size $m$.
- `sat3_to_independentSet_completeness`: $G_\varphi$ has IS of size $m \implies \varphi \in \text{3-SAT}$.
- `sat3_to_independentSet_correct`: Equivalence of 3-SAT and Independent Set.
- `independentSet_to_vertexCover_iff`: $(G, k) \in \text{IS} \iff (G, |V| - k) \in \text{VC}$.
- `independentSet_to_clique_iff`: $(G, k) \in \text{IS} \iff (\overline{G}, k) \in \text{Clique}$.
- `vertexCover_to_clique_iff`: $(G, |V| - k) \in \text{VC} \iff (\overline{G}, k) \in \text{Clique}$.

### Track 4: Mathlib Asymptotics (`Amort.Complexity.Asymptotics`)
- `isBigO_twoSATWork_atTop`: 2-SAT operations are $O(n + m)$ under `Filter.atTop`.
- `isBigO_polyEval_atTop`: Polynomial functions are $O((n+1)^k)$ under `Filter.atTop`.
- `isBigO_sat3ToIS_vertices_atTop`: Gadget vertex count is $O(m)$ under `Filter.atTop`.
- `isBigO_sat3ToIS_edges_atTop`: Gadget edge count is $O(m^2)$ under `Filter.atTop`.
- `isBigO_complementEdges_atTop`: Complement graph edge count is $O(n^2)$ under `Filter.atTop`.

---

## Verification & Axiom Audit

All modules build cleanly with:
```bash
lake build Amort
```
Verification statistics:
- **Build**: 0 warnings, 0 errors (2111 jobs).
- **Axioms**: `#print axioms` verifies zero use of `sorry` or `sorryAx`. All proofs rely exclusively on
  standard foundational Lean 4 axioms: `propext`, `Quot.sound`, `Classical.choice`.
- **Style**: 0 lines exceed 100 characters across all Lean files.
