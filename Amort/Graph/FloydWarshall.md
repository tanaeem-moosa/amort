# Floyd-Warshall All-Pairs Shortest Paths

> **Status: stub — not verified** (Phase 3 canon stub; state-space model is formulated,
> but bottom-up shortest path dynamic programming is a specification stub).


This document details the Lean 4 formalization of the textbook Floyd-Warshall dynamic programming
algorithm in `Amort.Graph.FloydWarshall`, establishing its 3D state space, Bellman intermediate
optimality recurrence, and $O(n^3)$ operational bound in the `Amort.Recurrence.DP` framework.

---

## 1. Problem Formulation & Weights

Given a directed graph on $n$ vertices (`Fin n`), edge weights are represented by a weight function
`W : Fin n → Fin n → WithTop ℕ`, where `⊤` denotes the absence of a directed edge and $W(i, i) = 0$:

```lean
def floydWarshallRec {n : ℕ} (W : Fin n → Fin n → WithTop ℕ) :
    ℕ → Fin n → Fin n → WithTop ℕ
  | 0, i, j => W i j
  | k + 1, i, j =>
    if h : k < n then
      min (floydWarshallRec W k i j)
          (floydWarshallRec W k i ⟨k, h⟩ + floydWarshallRec W k ⟨k, h⟩ j)
    else
      floydWarshallRec W k i j
```

The algorithm outputs the final all-pairs shortest distance matrix after considering all $n$ stages:

```lean
def floydWarshallAllPairs {n : ℕ} (W : Fin n → Fin n → WithTop ℕ) :
    Fin n → Fin n → WithTop ℕ :=
  floydWarshallRec W n
```

---

## 2. Invariants & Mathematical Properties

1. **Base Case**:
   ```lean
   @[simp]
   theorem floydWarshallRec_zero (W : Fin n → Fin n → WithTop ℕ) (i j : Fin n) :
       floydWarshallRec W 0 i j = W i j
   ```

2. **Monotonicity**:
   Distance estimates never increase as additional intermediate vertices are permitted:
   ```lean
   theorem floydWarshallRec_mono (W : Fin n → Fin n → WithTop ℕ)
       (k : ℕ) (i j : Fin n) :
       floydWarshallRec W (k + 1) i j ≤ floydWarshallRec W k i j

   theorem floydWarshallRec_le_of_le {k1 k2 : ℕ} (h : k1 ≤ k2) (i j : Fin n) :
       floydWarshallRec W k2 i j ≤ floydWarshallRec W k1 i j
   ```

3. **Diagonal Invariance**:
   Self-distances remain 0 throughout all stages:
   ```lean
   theorem floydWarshallRec_self (W : Fin n → Fin n → WithTop ℕ)
       (hW : ∀ i, W i i = 0) (k : ℕ) (i : Fin n) :
       floydWarshallRec W k i i = 0
   ```

4. **Intermediate Relaxation**:
   Each stage satisfies the triangle inequality through the $k$-th vertex:
   ```lean
   theorem floydWarshallRec_step_le_trans (k : ℕ) (h : k < n) (i j : Fin n) :
       floydWarshallRec W (k + 1) i j ≤
         floydWarshallRec W k i ⟨k, h⟩ + floydWarshallRec W k ⟨k, h⟩ j
   ```

---

## 3. 3D Dynamic Programming State Space & Complexity

The subproblem state space consists of triples $(k, i, j)$ where $k \in \text{Fin}(n + 1)$ indexes
the relaxation stage and $i, j \in \text{Fin } n$ index vertex pairs:

```lean
abbrev FWState (n : ℕ) : Type := Fin (n + 1) × Fin n × Fin n
```

### Exact Cardinality
```lean
theorem card_fw_states (n : ℕ) :
    Fintype.card (FWState n) = (n + 1) * n ^ 2
```

### Cubic State Bound
```lean
theorem card_fw_states_le_cube (n : ℕ) :
    (n + 1) * n ^ 2 ≤ (n + 1) ^ 3
```

### DPModel Instantiation & Operational Work
Instantiating `Amort.Recurrence.DPModel` on `FWState n` with unit cost per transition ($C = 1$):

```lean
def floydWarshallDP (n : ℕ) : DPModel (FWState n) where
  costPerState := fun _ ↦ 1
  costBound := 1
  h_cost := fun _ ↦ Nat.le_refl 1

theorem floydWarshallDP_totalCost (n : ℕ) :
    (floydWarshallDP n).totalCost = (n + 1) * n ^ 2

theorem floydWarshallDP_totalCost_le (n : ℕ) :
    (floydWarshallDP n).totalCost ≤ (n + 1) * n ^ 2

theorem floydWarshallDP_totalCost_le_cube (n : ℕ) :
    (floydWarshallDP n).totalCost ≤ (n + 1) ^ 3
```

Under `Filter.atTop`, `(floydWarshallDP n).totalCost = O(n^3)`.
