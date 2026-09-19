# Karp's Foundational Reductions: 3-SAT, Independent Set, Vertex Cover, and Clique

## Overview

The `Amort.Complexity.KarpReductions` module formalizes Karp's foundational reduction chain
and the classical Complement Duality Theorem in Lean 4:
1. **Simple Graph Framework**: `SimpleGraph V` with symmetric, loopless adjacency.
2. **Combinatorial Graph Problems**:
   - `IsIndependentSet G S`: Pairwise non-adjacent vertex subset.
   - `IsVertexCover G S`: Subset meeting every edge.
   - `IsClique G S`: Pairwise adjacent vertex subset.
   - `complement G`: Complement graph $\overline{G}$ where $u \sim_{\overline{G}} v \iff u \ne v \wedge \neg(u \sim_G v)$.
3. **Complement Duality Theorem**:
   For any graph $G = (V, E)$ and subset $S \subseteq V$:
   $$S \text{ is an Independent Set in } G \iff V \setminus S \text{ is a Vertex Cover in } G \iff S \text{ is a Clique in } \overline{G}$$
4. **3-SAT to Independent Set Reduction (Clause Triangle Gadgets)**:
   - For each clause $i \in \{0, \dots, m-1\}$, a triangle $K_3$ of vertices $(i, 0), (i, 1), (i, 2)$.
   - Conflict edges between contradictory literals $l_1 = \neg l_2$ across different clauses.
   - Soundness and Completeness: $\varphi$ is satisfiable $\iff G_\varphi$ contains an independent set of size $m$.
5. **Reduction Chain**:
   $$\text{3-SAT} \le_P \text{Independent Set} \le_P \text{Vertex Cover} \le_P \text{Clique}$$

---

## Complement Duality Theorem

### Formal Statements

```lean
-- Part 1: Independent Set <-> Vertex Cover
theorem isIndependentSet_iff_isVertexCover_compl [Fintype V] (G : SimpleGraph V) (S : Finset V) :
    G.IsIndependentSet S ↔ G.IsVertexCover (Sᶜ)

-- Part 2: Independent Set <-> Clique in Complement
theorem isIndependentSet_iff_isClique_complement (G : SimpleGraph V) (S : Finset V) :
    G.IsIndependentSet S ↔ G.complement.IsClique S

-- Master Tripartite Duality
theorem complement_duality [Fintype V] (G : SimpleGraph V) (S : Finset V) :
    (G.IsIndependentSet S ↔ G.IsVertexCover (Sᶜ)) ∧
    (G.IsIndependentSet S ↔ G.complement.IsClique S) ∧
    (G.IsVertexCover (Sᶜ) ↔ G.complement.IsClique S)
```

### Problem Reductions via Duality
- **Independent Set $\to$ Vertex Cover**: $(G, k) \mapsto (G, |V| - k)$.
  $$\exists S, \text{IsIndependentSet } G\ S \wedge |S| = k \iff \exists C, \text{IsVertexCover } G\ C \wedge |C| = |V| - k$$
- **Independent Set $\to$ Clique**: $(G, k) \mapsto (\overline{G}, k)$.
  $$\exists S, \text{IsIndependentSet } G\ S \wedge |S| = k \iff \exists K, \text{IsClique } \overline{G}\ K \wedge |K| = k$$
- **Vertex Cover $\to$ Clique**: $(G, |V| - k) \mapsto (\overline{G}, k)$.

---

## 3-SAT to Independent Set Gadget Reduction

### Construction
Given a 3-CNF formula $\varphi$ with $m$ clauses:
1. **Vertices**: $V = \text{Fin } m \times \text{Fin } 3$, total $3m$ vertices.
   Vertex $(i, j)$ represents the $j$-th literal of clause $i$.
2. **Clause Triangle Edges**: For each clause $i$, vertices $(i, 0), (i, 1), (i, 2)$ form a triangle $K_3$.
3. **Conflict Edges**: An edge connects $(i_1, j_1)$ and $(i_2, j_2)$ if $i_1 \ne i_2$ and their literals are negations of each other:
   $$l(i_1, j_1) = \neg l(i_2, j_2)$$

### Soundness Proof (`sat3_to_independentSet_soundness`)
Suppose $\tau \models \varphi$. For each clause $i \in \{0, \dots, m-1\}$, choose the first literal position
$j_i \in \{0, 1, 2\}$ such that $\tau(l(i, j_i)) = \text{true}$.
Let $S = \{ (i, j_i) \mid i \in \text{Fin } m \}$.
- $|S| = m$ because $i \mapsto (i, j_i)$ is injective.
- No two vertices in $S$ share a clause index (no clause triangle edges).
- No two vertices in $S$ have conflicting literals, because both evaluate to `true` under $\tau$ (no conflict edges).
Hence $S$ is an independent set of size $m$.

### Completeness Proof (`sat3_to_independentSet_completeness`)
Suppose $G_\varphi$ contains an independent set $S$ with $|S| = m$.
1. **At Most One per Clause**: Since the 3 vertices of each clause form a triangle $K_3$, $S$ can contain at most 1 vertex from each clause.
2. **Exactly One per Clause**: The projection $\pi(i, j) = i$ is injective on $S$.
   Since $|S| = m$ and there are $m$ clauses, $\pi(S) = \text{Fin } m$. Thus $S$ contains exactly one vertex per clause!
3. **Consistency**: Since $S$ is an independent set, no two vertices in $S$ are connected by conflict edges.
   Hence $\{ l(u) \mid u \in S \}$ contains no literal and its negation.
4. **Satisfying Model**: Setting $\tau(x) = \text{true} \iff \text{pos } x \in \{ l(u) \mid u \in S \}$
   evaluates every literal in $S$ to `true`.
   Since every clause contains a representative in $S$, all $m$ clauses are satisfied!

---

## Axiom Audit

All reduction theorems are formally verified with 0 `sorry` and 0 `sorryAx`, relying strictly on standard Lean 4 axioms (`propext`, `Classical.choice`, `Quot.sound`).
