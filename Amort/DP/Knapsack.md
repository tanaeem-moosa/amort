# Grid Dynamic Programming: 0/1 Knapsack Problem

This document details the Lean 4 formalization of the textbook 0/1 Knapsack dynamic programming
algorithm in `Amort.DP.Knapsack`, proving mathematical correctness against arbitrary item
subcollections, and instantiating `Amort.Recurrence.GridDP` to prove the $O(n \cdot W)$ complexity.

---

## 1. Problem Formulation and Recurrence

An instance of the 0/1 Knapsack problem consists of $n$ items with weights $w_i \in \mathbb{N}$
and values $v_i \in \mathbb{N}$, and a knapsack weight capacity $W \in \mathbb{N}$:

```lean
structure Item where
  weight : ℕ
  value : ℕ
```

### 1.1 Bellman Recurrence
The dynamic programming recurrence evaluates whether to include item $i$:
$$K(0, w) = 0$$
$$K(i+1, w) = \begin{cases}
  K(i, w) & \text{if } w < w_i \\
  \max(K(i, w), v_i + K(i, w - w_i)) & \text{if } w \ge w_i
\end{cases}$$

Formalized as:
```lean
def knapsackRec (w v : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | i + 1, cap =>
    if cap < w i then
      knapsackRec w v i cap
    else
      max (knapsackRec w v i cap) (v i + knapsackRec w v i (cap - w i))
```

Monotonicity in capacity is proven:
```lean
theorem knapsackRec_mono_cap (w v : ℕ → ℕ) (n : ℕ) {c1 c2 : ℕ} (hc : c1 ≤ c2) :
    knapsackRec w v n c1 ≤ knapsackRec w v n c2
```

---

## 2. Mathematical Correctness: Soundness, Completeness, and Optimality

Subcollections of the first $n$ items are modeled as subsets $s \subseteq \{0, \dots, n-1\}$
(`s ⊆ Finset.range n`):

```lean
def totalWeight (w : ℕ → ℕ) (s : Finset ℕ) : ℕ := ∑ j ∈ s, w j
def totalValue (v : ℕ → ℕ) (s : Finset ℕ) : ℕ := ∑ j ∈ s, v j
def IsFeasibleSubcollection (w : ℕ → ℕ) (s : Finset ℕ) (cap : ℕ) : Prop :=
  totalWeight w s ≤ cap
```

### 2.1 Soundness (Upper Bound)
Every feasible subcollection $s$ satisfies $\text{totalValue } v \; s \le K(n, \text{cap})$:

```lean
theorem knapsack_sound (w v : ℕ → ℕ) (n cap : ℕ) (s : Finset ℕ)
    (hs : s ⊆ Finset.range n) (h_cap : totalWeight w s ≤ cap) :
    totalValue v s ≤ knapsackRec w v n cap
```

*Proof Strategy*: Induction on $n$. If $n \in s$, we erase $n$ to obtain $s' \subseteq \text{range } n$
with total weight $\le \text{cap} - w_n$, applying the induction hypothesis. If $n \notin s$, $s$ is
directly a subset of $\text{range } n$.

### 2.2 Completeness (Witness Existence)
There exists a feasible subset achieving the exact dynamic programming value:

```lean
theorem knapsack_complete (w v : ℕ → ℕ) (n cap : ℕ) :
    ∃ s : Finset ℕ, s ⊆ Finset.range n ∧ totalWeight w s ≤ cap ∧
      totalValue v s = knapsackRec w v n cap
```

### 2.3 Optimality
Together, soundness and completeness prove that $K(n, \text{cap})$ is the exact maximum:

```lean
theorem knapsack_is_optimal (w v : ℕ → ℕ) (n cap : ℕ) :
    (∀ s ⊆ Finset.range n, totalWeight w s ≤ cap →
      totalValue v s ≤ knapsackRec w v n cap) ∧
    (∃ s ⊆ Finset.range n, totalWeight w s ≤ cap ∧
      totalValue v s = knapsackRec w v n cap)
```

---

## 3. Grid DP Instantiation and Complexity

The dynamic programming table forms an $(n + 1) \times (W + 1)$ grid on
$\text{Fin}(n + 1) \times \text{Fin}(W + 1)$:

```lean
def knapsackGridDP (n W : ℕ) : GridDP n W :=
  GridDP.unitGridDP n W
```

By `GridDP.unitGridDP_totalCost`:
```lean
theorem knapsackGridDP_totalCost (n W : ℕ) :
    (knapsackGridDP n W).toDPModel.totalCost = (n + 1) * (W + 1)

theorem knapsackGridDP_totalCost_le (n W : ℕ) :
    (knapsackGridDP n W).toDPModel.totalCost ≤ (n + 1) * (W + 1)
```

Under `Filter.atTop` on $\mathbb{N} \times \mathbb{N}$:
```lean
theorem isBigO_knapsackGridDP_totalCost_atTop :
    (fun (p : ℕ × ℕ) ↦ (((knapsackGridDP p.1 p.2).toDPModel.totalCost : ℕ) : ℝ)) =O[Filter.atTop]
      (fun p ↦ ((p.1 * p.2 : ℕ) : ℝ))
```
