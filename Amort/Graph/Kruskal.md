# Kruskal's Minimum Spanning Tree Algorithm

This document details the Lean 4 formalization of Kruskal's Minimum Spanning Tree (MST)
algorithm in `Amort.Graph.Kruskal`, connecting edge sorting to `Amort.Sorting.MergeSort`,
establishing the $O(|E| \log |V|)$ overall time complexity, and proving greedy Cut-Property
optimality.

---

## 1. Edge Weight Ordering & Merge Sort Connection

Undirected weighted edges are represented as structures:

```lean
structure Edge (n : ℕ) where
  u : Fin n
  v : Fin n
  w : ℕ
deriving DecidableEq, Repr
```

Edges are sorted by weight using `List.mergeSort` via `Amort.Sorting.MergeSort`:

```lean
def edgeWeightLe {n : ℕ} (e1 e2 : Edge n) : Bool := e1.w ≤ e2.w

theorem kruskal_sort_bound {n : ℕ} (edges : List (Edge n)) :
    List.mergeSortCount edgeWeightLe edges ≤ edges.length * Nat.size edges.length
```

This establishes the initial edge sorting phase complexity:
$$O(|E| \log |E|) = O(|E| \log |V|)$$
since $|E| \le |V|^2$ in simple graphs.

---

## 2. Greedy Edge Selection & Cut-Property Optimality

A cut in a graph is a partition $(S, S^c)$ of vertices. An edge crosses cut $S$ if exactly
one of its endpoints belongs to $S$:

```lean
def CrossesCut {n : ℕ} (S : Fin n → Prop) (e : Edge n) : Prop :=
  (S e.u ∧ ¬ S e.v) ∨ (S e.v ∧ ¬ S e.u)
```

An edge is a minimal cut edge if it has minimal weight among all candidate edges crossing $S$:

```lean
def IsMinCutEdge {n : ℕ} (E : List (Edge n)) (S : Fin n → Prop) (e : Edge n) : Prop :=
  e ∈ E ∧ CrossesCut S e ∧ ∀ e' ∈ E, CrossesCut S e' → e.w ≤ e'.w
```

### Cut-Property Optimality Theorem
When Kruskal selects the first edge from a sorted list that crosses cut $S$, it is guaranteed
to be a minimum-weight edge crossing $S$:

```lean
theorem head_min_cut_edge_of_sorted {n : ℕ} (e : Edge n) (rest : List (Edge n))
    (S : Fin n → Prop)
    (h_cross : CrossesCut S e)
    (h_sorted : ∀ e' ∈ rest, e.w ≤ e'.w) :
    IsMinCutEdge (e :: rest) S e
```

Proof Strategy:
Any other edge $e'$ crossing $S$ either is $e$ (so $e.w \le e'.w$) or belongs to $rest$,
where $e.w \le e'.w$ follows by sortedness of the edge list.

---

## 3. Total Operational Complexity ($O(|E| \log |V|)$)

Kruskal's algorithm executes two sequential phases:
1. **Edge Sorting**: $|E| \cdot \text{Nat.size } |E|$ comparisons.
2. **DSU Processing**: For each edge, 2 `find` operations and at most 1 `union`, costing
   $\le 4 \cdot \text{Nat.size } |V| + 2$ per edge, plus $|V|$ initialization steps.

```lean
def kruskalTotalWork (numV numE : ℕ) : ℕ :=
  numE * Nat.size numE + numE * (4 * Nat.size numV + 2) + numV
```

### Combined Linear-Logarithmic Bound
In simple graphs where $|E| \le |V|^2$, $\text{Nat.size } |E| \le 2 \cdot \text{Nat.size } |V| + 1$:

```lean
theorem kruskal_total_work_le (numV numE : ℕ) (hE : Nat.size numE ≤ 2 * Nat.size numV + 1) :
    kruskalTotalWork numV numE ≤ (6 * Nat.size numV + 3) * numE + numV
```

Under `Filter.atTop`, this establishes overall time complexity:
$$\text{Total Work} = O(|E| \log |V|)$$
