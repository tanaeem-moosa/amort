# 2-SAT Linear-Time Solver via Strongly Connected Components

## Overview

The `Amort.Complexity.TwoSAT` module formalizes the linear-time 2-SAT algorithm via reduction
to Strongly Connected Components (SCC) in the implication digraph:
1. **2-CNF Formulas**: Collections of 2-literal disjunctions $(l_1 \vee l_2)$ over variables `Fin n`.
2. **Implication Digraph**: Each clause $(u \vee v)$ generates two directed edges $\neg u \to v$
   and $\neg v \to u$.
3. **Contrapositive Path Symmetry**:
   $$u \rightsquigarrow v \iff \neg v \rightsquigarrow \neg u$$
4. **Implication Preservation**: Truth valuations are preserved along implication paths:
   $$\tau \models \varphi \wedge u \rightsquigarrow v \wedge \tau(u) = \text{true} \implies \tau(v) = \text{true}$$
5. **Soundness (Obstruction)**: If for some variable $x$, $x \rightsquigarrow \neg x$ and
   $\neg x \rightsquigarrow x$, then $\varphi$ is unsatisfiable.
6. **Completeness (Model Construction)**: If no variable $x$ lies in the same SCC as $\neg x$,
   then $\varphi$ is satisfiable.
7. **Equivalence Theorem**: $\varphi$ is satisfiable $\iff \forall x, \neg(x \approx \neg x)$.
8. **Bridge to `Amort.Graph.SCC`**: Bijective mapping between literals and `Fin (2 * n)`, connecting
   to `Amort.Graph.Reachable`, `Amort.Graph.MutuallyReachable`, and Kosaraju's algorithm work model.
9. **Linear Operational Bound**: $O(|V| + |E|) = O(n + m)$.

---

## Mathematical Architecture

### Literals and Negation
```lean
inductive Lit (n : ℕ) : Type
  | pos (v : Fin n) : Lit n
  | neg (v : Fin n) : Lit n

def notLit : Lit n → Lit n
  | Lit.pos v => Lit.neg v
  | Lit.neg v => Lit.pos v
```
- Involutive: $\neg(\neg l) = l$.
- Irreflexive: $\neg l \ne l$.
- Fintype: cardinality is $2n$.

### Implication Digraph & Reachability
For clause $(u \vee v) \in \varphi$:
- Edge 1: $\neg u \to v$
- Edge 2: $\neg v \to u$
- Contrapositive Symmetry:
  `ImplicationEdge φ u v ↔ ImplicationEdge φ (notLit v) (notLit u)`
  `ImplReachable φ u v → ImplReachable φ (notLit v) (notLit u)`

### Conflict Reachability Lemma
$$\text{If } u \rightsquigarrow v \text{ and } u \rightsquigarrow \neg v, \text{ then } u \rightsquigarrow \neg u.$$
Proof: by contrapositive, $u \rightsquigarrow \neg v \implies v \rightsquigarrow \neg u$.
Then by transitivity, $u \rightsquigarrow v \rightsquigarrow \neg u$.

---

## Soundness and Completeness Proof Strategy

### 1. Soundness (`twoSAT_soundness`)
Suppose $\tau \models \varphi$ and $x \approx \neg x$:
- If $\tau(x) = \text{true}$, then $\text{pos } x = \text{true}$.
  Since $\text{pos } x \rightsquigarrow \text{neg } x$, $\text{neg } x = \text{true}$, so $\tau(x) = \text{false}$, contradiction.
- If $\tau(x) = \text{false}$, then $\text{neg } x = \text{true}$.
  Since $\text{neg } x \rightsquigarrow \text{pos } x$, $\text{pos } x = \text{true}$, so $\tau(x) = \text{true}$, contradiction.
Hence $\forall x, \neg (\text{pos } x \approx \text{neg } x)$.

### 2. Completeness (`twoSAT_completeness`)
We construct a satisfying assignment by considering the family $\mathcal{S}$ of subsets
$S \subseteq \text{Lit } n$ that are:
1. **Closed**: $\forall u \in S, \forall v, u \rightsquigarrow v \implies v \in S$.
2. **Consistent**: $\forall u \in S, \neg u \notin S$.

Since $\emptyset \in \mathcal{S}$ and $\text{Lit } n$ is finite, there exists a set $S^* \in \mathcal{S}$
of maximal cardinality.

**Maximality implies Completeness**:
If $S^*$ were not complete, there exists $u$ such that $u \notin S^*$ and $\neg u \notin S^*$.
We prove that at least one of $S^* \cup R(u)$ or $S^* \cup R(\neg u)$ is consistent (where
$R(l) = \{ v \mid l \rightsquigarrow v \}$):
- If $S^* \cup R(u)$ is inconsistent, then $u \rightsquigarrow \neg u$.
- If $S^* \cup R(\neg u)$ is inconsistent, then $\neg u \rightsquigarrow u$.
- If both were inconsistent, $u \approx \neg u$, contradicting the hypothesis!
Hence at least one extension is consistent and strictly larger than $S^*$, contradicting maximality.
Therefore $S^*$ is complete!

**Model Assignment**:
Define $\tau(v) := (\text{pos } v \in S^*)$.
For any clause $(u \vee v) \in \varphi$:
If $\tau(u) = \text{false}$, then $u \notin S^*$, so $\neg u \in S^*$ (by completeness).
Since $\neg u \to v$ is an implication edge and $S^*$ is closed, $v \in S^*$, so $\tau(v) = \text{true}$!
Thus $\tau$ satisfies every clause of $\varphi$!

---

## Operational Complexity

Kosaraju's two-pass DFS on $2n$ vertices and $2m$ edges executes in $2(2n + 2m) = 4(n + m)$ steps.
Including graph construction ($2m$) and SCC consistency check ($n$):
$$\text{twoSATWork}(n, m) = 5n + 6m \le 6(n + m) = O(|V| + |E|)$$
This linear bound is formally connected to `Mathlib.Analysis.Asymptotics.IsBigO`.
