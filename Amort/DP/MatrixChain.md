# Interval Dynamic Programming: Matrix Chain Multiplication

This document details the Lean 4 formalization of the textbook Matrix Chain Multiplication
algorithm in `Amort.DP.MatrixChain`, establishing its interval state space, Bellman optimality
recurrence, and $O(n^3)$ operational bound in the `Amort.Recurrence.DP` framework.

---

## 1. Problem Formulation and Dimensions

Given a sequence of $n$ matrices $A_0, A_1, \dots, A_{n-1}$ where matrix $A_i$ has dimension
$p_i \times p_{i+1}$, the dimensions are given by a list or sequence $p_0, p_1, \dots, p_n$:

```lean
def dimsOfList (dims : List ℕ) : ℕ → ℕ := fun i ↦ dims.getD i 0
```

Multiplying two matrices of dimensions $p_i \times p_{k+1}$ and $p_{k+1} \times p_{j+1}$ requires
$p_i \cdot p_{k+1} \cdot p_{j+1}$ scalar operations:

```lean
def scalarMultCost (p : ℕ → ℕ) (i k j : ℕ) : ℕ :=
  p i * p (k + 1) * p (j + 1)
```

For any split position $k$ with $i \le k < j$:

```lean
def splitCost (p : ℕ → ℕ) (M : ℕ → ℕ → ℕ) (i j k : ℕ) : ℕ :=
  M i k + M (k + 1) j + scalarMultCost p i k j
```

---

## 2. Bellman Recurrence

The minimal multiplication cost $M(i, j)$ satisfies the Bellman dynamic programming recurrence:
$$M(i, i) = 0$$
$$M(i, j) = \min_{i \le k < j} \{ M(i, k) + M(k + 1, j) + p_i \cdot p_{k+1} \cdot p_{j+1} \}$$

In Lean 4, this is formalized with bounded length:

```lean
def matrixChainCostLen (p : ℕ → ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | len + 1, i, j =>
    if i < j ∧ j - i ≤ len + 1 then
      listMin ((List.range (j - i)).map (fun d ↦
        splitCost p (matrixChainCostLen p len) i j (i + d)))
    else
      0

def matrixChainCost (p : ℕ → ℕ) (i j : ℕ) : ℕ :=
  matrixChainCostLen p (j - i) i j
```

The base case is formally proven:
```lean
@[simp]
theorem matrixChainCost_self (p : ℕ → ℕ) (i : ℕ) : matrixChainCost p i i = 0
```

---

## 3. Interval State Space and Cardinality

Subproblems correspond to intervals $0 \le i \le j < n$, formalized as a subtype:

```lean
def IntervalState (n : ℕ) : Type :=
  { p : Fin n × Fin n // p.1.val ≤ p.2.val }
```

### 3.1 Sigma Type Equivalence
By pairing each right endpoint $j < n$ with a left endpoint $i \le j$ ($i < j + 1$):

```lean
def intervalStateEquiv (n : ℕ) : IntervalState n ≃ (j : Fin n) × Fin (j.val + 1)
```

This establishes that the state space cardinality equals the triangular sum:
```lean
theorem card_intervalState_eq_sum (n : ℕ) :
    Fintype.card (IntervalState n) = ∑ j : Fin n, (j.val + 1)
```

### 3.2 Exact and Quadratic Cardinality Bounds
Using `Finset.sum_range_id`:
```lean
theorem card_intervalState (n : ℕ) :
    Fintype.card (IntervalState n) = n * (n + 1) / 2

theorem card_intervalState_le (n : ℕ) :
    Fintype.card (IntervalState n) ≤ n ^ 2
```

---

## 4. State-Space Complexity via `Amort.Recurrence.DP`

Each interval $(i, j)$ evaluates $j - i \le n$ split points $k$. We embed this into `DPModel`:

```lean
def matrixChainDP (n : ℕ) : DPModel (IntervalState n) where
  costPerState := fun ⟨⟨i, j⟩, _⟩ ↦ j.val - i.val
  costBound := n
  h_cost := fun ⟨⟨_i, j⟩, _⟩ ↦ by ...
```

By the fundamental state-space DP theorem `DPModel.totalCost_le`:
$$\text{totalCost} \le |IntervalState n| \cdot \text{costBound} \le n^2 \cdot n = n^3$$

```lean
theorem matrixChainDP_totalCost_le (n : ℕ) :
    (matrixChainDP n).totalCost ≤ n ^ 3

theorem matrixChainDP_totalCost_le_triangular_mul (n : ℕ) :
    (matrixChainDP n).totalCost ≤ (n * (n + 1) / 2) * n
```

Under `Filter.atTop` on $\mathbb{N}$:
```lean
theorem isBigO_matrixChainDP_totalCost_atTop :
    (fun n ↦ (((matrixChainDP n).totalCost : ℕ) : ℝ)) =O[Filter.atTop]
      (fun n ↦ ((n ^ 3 : ℕ) : ℝ))
```
