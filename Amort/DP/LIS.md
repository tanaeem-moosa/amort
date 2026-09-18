# Dynamic Programming: Longest Increasing Subsequence (LIS)

This document details the Lean 4 formalization of the textbook Longest Increasing Subsequence
(LIS) algorithm in `Amort.DP.LIS`, proving mathematical correctness against all strictly
increasing subsequences, and establishing its $O(n^2)$ complexity bound in `Amort.Recurrence.DP`.

---

## 1. Subsequence Predicates and Formulations

For a sequence $xs : \text{List } \mathbb{N}$, a strictly increasing subsequence is defined as:

```lean
def IsStrictlyIncreasingSubsequence (sub xs : List ℕ) : Prop :=
  sub.Sublist xs ∧ sub.Pairwise (· < ·)

def IsStrictlyIncreasingSubsequenceWithPrefix (prev : ℕ) (sub xs : List ℕ) : Prop :=
  sub.Sublist xs ∧ sub.Pairwise (· < ·) ∧ (∀ y ∈ sub, prev < y)
```

### 1.1 Recursive Bellman Formulations
The subproblem characterization parameterized by a lower bound `prev`:

```lean
def lisWithPrefix (prev : ℕ) : List ℕ → ℕ
  | [] => 0
  | x :: xs =>
    if prev < x then
      max (lisWithPrefix prev xs) (1 + lisWithPrefix x xs)
    else
      lisWithPrefix prev xs

def lisRec : List ℕ → ℕ
  | [] => 0
  | x :: xs => max (lisRec xs) (1 + lisWithPrefix x xs)
```

---

## 2. Mathematical Correctness

### 2.1 Soundness
Every strictly increasing subsequence has length bounded by `lisRec xs`:

```lean
lemma lisWithPrefix_sound (prev : ℕ) (xs sub : List ℕ)
    (h : IsStrictlyIncreasingSubsequenceWithPrefix prev sub xs) :
    sub.length ≤ lisWithPrefix prev xs

theorem lisRec_sound (xs sub : List ℕ)
    (h : IsStrictlyIncreasingSubsequence sub xs) :
    sub.length ≤ lisRec xs
```

### 2.2 Completeness
Constructive existence of an increasing subsequence achieving the computed length:

```lean
lemma lisWithPrefix_complete (prev : ℕ) (xs : List ℕ) :
    ∃ sub, IsStrictlyIncreasingSubsequenceWithPrefix prev sub xs ∧
      sub.length = lisWithPrefix prev xs

theorem lisRec_complete (xs : List ℕ) :
    ∃ sub, IsStrictlyIncreasingSubsequence sub xs ∧ sub.length = lisRec xs
```

### 2.3 Optimality
```lean
theorem lis_is_optimal (xs : List ℕ) :
    (∀ sub, IsStrictlyIncreasingSubsequence sub xs → sub.length ≤ lisRec xs) ∧
    (∃ sub, IsStrictlyIncreasingSubsequence sub xs ∧ sub.length = lisRec xs)
```

---

## 3. Predecessor State-Space Model and Complexity

The standard dynamic programming algorithm for LIS computes $L(i)$ for each state $i \in \text{Fin } n$
by examining all predecessors $j < i$ with $xs[j] < xs[i]$.

The number of predecessors examined at state $i$ is $i \le n$. We embed this into `DPModel`:

```lean
def lisDP (n : ℕ) : DPModel (Fin n) where
  costPerState := fun i ↦ i.val
  costBound := n
  h_cost := fun i ↦ by ...
```

### 3.1 Exact and Quadratic Bounds
The total work is the triangular sum:
$$\text{totalCost} = \sum_{i=0}^{n-1} i = \frac{n(n - 1)}{2} \le \frac{n(n + 1)}{2} \le n^2$$

```lean
theorem lisDP_totalCost_eq (n : ℕ) :
    (lisDP n).totalCost = n * (n - 1) / 2

theorem lisDP_totalCost_le_triangular (n : ℕ) :
    (lisDP n).totalCost ≤ n * (n + 1) / 2

theorem lisDP_totalCost_le_sq (n : ℕ) :
    (lisDP n).totalCost ≤ n ^ 2
```

Under `Filter.atTop` on $\mathbb{N}$:
```lean
theorem isBigO_lisDP_totalCost_atTop :
    (fun n ↦ (((lisDP n).totalCost : ℕ) : ℝ)) =O[Filter.atTop]
      (fun n ↦ ((n ^ 2 : ℕ) : ℝ))
```
