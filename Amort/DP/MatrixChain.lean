/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Amort.Recurrence.DP
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod

/-!
# Interval Dynamic Programming: Matrix Chain Multiplication

This module formalizes the textbook Matrix Chain Multiplication dynamic programming
algorithm and its $O(n^3)$ complexity bound in the `Amort.Recurrence.DP` state-space
complexity framework.

## Mathematical Architecture

1. **Matrix Dimensions & Scalar Multiplications**:
   A chain of $n$ matrices $A_0, \dots, A_{n-1}$ is represented by dimensions $p_0, \dots, p_n$
   where $A_i$ has dimension $p_i \times p_{i+1}$.
   Splitting the chain at index $k$ ($i \le k < j$) requires multiplying subchain
   $(A_i \dots A_k)$ of dimension $p_i \times p_{k+1}$ with $(A_{k+1} \dots A_j)$ of dimension
   $p_{k+1} \times p_{j+1}$, taking $p_i \cdot p_{k+1} \cdot p_{j+1}$ scalar operations.

2. **Bellman Recurrence**:
   $$M(i, i) = 0$$
   $$M(i, j) = \min_{i \le k < j} \{ M(i, k) + M(k + 1, j) + p_i \cdot p_{k+1} \cdot p_{j+1} \}$$

3. **Interval State Space**:
   The subproblems correspond to intervals $0 \le i \le j < n$, formalized as
   `IntervalState n := { p : Fin n × Fin n // p.1.val ≤ p.2.val }`.
   The state space cardinality is:
   $$|IntervalState n| = \sum_{j=0}^{n-1} (j + 1) = \frac{n(n + 1)}{2} \le n^2$$

4. **State-Space Complexity**:
   At each state $(i, j)$, the algorithm evaluates $j - i \le n$ split choices ($c(i, j) \le n$).
   Instantiating `Amort.Recurrence.DPModel` on `IntervalState n` with uniform bound $n$ proves:
   $$\text{Total Work} \le |IntervalState n| \cdot n \le n^2 \cdot n = n^3$$
-/

namespace Amort.DP

open BigOperators
open Amort.Recurrence

/-! ### Dimensions and Split Cost Model -/

/-- Extracts dimensions from a list of lengths $p_0, \dots, p_n$. -/
def dimsOfList (dims : List ℕ) : ℕ → ℕ := fun i ↦ dims.getD i 0

/-- Cost of scalar multiplications required to multiply product matrices $(A_i \dots A_k)$
and $(A_{k+1} \dots A_j)$ given dimension sequence `p`. -/
def scalarMultCost (p : ℕ → ℕ) (i k j : ℕ) : ℕ :=
  p i * p (k + 1) * p (j + 1)

/-- Combined cost of splitting chain $(A_i \dots A_j)$ at position $k$, given a subproblem
cost function `M`. -/
def splitCost (p : ℕ → ℕ) (M : ℕ → ℕ → ℕ) (i j k : ℕ) : ℕ :=
  M i k + M (k + 1) j + scalarMultCost p i k j

/-- Evaluates the minimum of a list of natural numbers, defaulting to 0 for the empty list. -/
def listMin : List ℕ → ℕ
  | [] => 0
  | x :: xs => xs.foldl min x

/-- Bounded-length recursive Bellman cost function. -/
def matrixChainCostLen (p : ℕ → ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | len + 1, i, j =>
    if i < j ∧ j - i ≤ len + 1 then
      listMin ((List.range (j - i)).map (fun d ↦
        splitCost p (matrixChainCostLen p len) i j (i + d)))
    else
      0

/-- Bellman dynamic programming cost function $M(i, j)$ representing the minimal scalar
multiplications to compute $A_i \dots A_j$. -/
def matrixChainCost (p : ℕ → ℕ) (i j : ℕ) : ℕ :=
  matrixChainCostLen p (j - i) i j

/-- Base case: computing a single matrix $A_i$ costs 0 multiplications. -/
@[simp]
theorem matrixChainCost_self (p : ℕ → ℕ) (i : ℕ) : matrixChainCost p i i = 0 := by
  dsimp [matrixChainCost]
  rw [Nat.sub_self]
  rfl

/-! ### Interval State Space -/

/-- The interval state space of pairs $(i, j)$ with $0 \le i \le j < n$. -/
def IntervalState (n : ℕ) : Type :=
  { p : Fin n × Fin n // p.1.val ≤ p.2.val }

instance (n : ℕ) : Fintype (IntervalState n) :=
  Subtype.fintype (fun p : Fin n × Fin n ↦ p.1.val ≤ p.2.val)

/-- Natural equivalence between interval states and sigma-types indexed by the right endpoint. -/
def intervalStateEquiv (n : ℕ) : IntervalState n ≃ (j : Fin n) × Fin (j.val + 1) where
  toFun := fun ⟨⟨i, j⟩, h⟩ ↦ ⟨j, ⟨i.val, Nat.lt_succ_of_le h⟩⟩
  invFun := fun ⟨j, ⟨i, hi⟩ ⟩ ↦
    ⟨⟨⟨i, lt_of_lt_of_le hi (Nat.succ_le_of_lt j.isLt)⟩, j⟩, Nat.le_of_lt_succ hi⟩
  left_inv := by
    rintro ⟨⟨⟨i, _⟩, ⟨j, _⟩⟩, _⟩
    rfl
  right_inv := by
    rintro ⟨⟨j, _⟩, ⟨i, _⟩⟩
    rfl

/-- Cardinality of `IntervalState n` expressed as the sum of $(j + 1)$ for $j < n$. -/
theorem card_intervalState_eq_sum (n : ℕ) :
    Fintype.card (IntervalState n) = ∑ j : Fin n, (j.val + 1) := by
  rw [Fintype.card_congr (intervalStateEquiv n)]
  rw [Fintype.card_sigma]
  simp

lemma sum_range_succ_id (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), i = n * (n + 1) / 2 := by
  have h := Finset.sum_range_id (n + 1)
  have h_sub : n + 1 - 1 = n := rfl
  rw [h_sub] at h
  rw [h, mul_comm]

lemma sum_range_add_one_eq (n : ℕ) :
    ∑ i ∈ Finset.range n, (i + 1) = ∑ i ∈ Finset.range (n + 1), i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ (fun i ↦ i + 1)]
    rw [Finset.sum_range_succ (fun i ↦ i)]
    rw [ih]

/-- Sum of $(i + 1)$ over `Finset.range n` is the triangular number $n(n + 1)/2$. -/
theorem sum_range_add_one (n : ℕ) :
    ∑ i ∈ Finset.range n, (i + 1) = n * (n + 1) / 2 := by
  rw [sum_range_add_one_eq, sum_range_succ_id]

/-- Exact cardinality of the interval state space: $|IntervalState n| = n(n + 1)/2$. -/
theorem card_intervalState (n : ℕ) :
    Fintype.card (IntervalState n) = n * (n + 1) / 2 := by
  rw [card_intervalState_eq_sum]
  rw [Fin.sum_univ_eq_sum_range (fun i ↦ i + 1) n]
  exact sum_range_add_one n

/-- Quadratic upper bound on the interval state space: $|IntervalState n| \le n^2$. -/
theorem card_intervalState_le (n : ℕ) :
    Fintype.card (IntervalState n) ≤ n ^ 2 := by
  have h := Fintype.card_subtype_le (fun p : Fin n × Fin n ↦ p.1.val ≤ p.2.val)
  simp only [Fintype.card_prod, Fintype.card_fin] at h
  rw [sq]
  exact h

/-! ### State-Space Dynamic Programming Model -/

/-- The state-space DP model for Matrix Chain Multiplication on `IntervalState n`,
where state $(i, j)$ evaluates $j - i \le n$ split choices. -/
def matrixChainDP (n : ℕ) : DPModel (IntervalState n) where
  costPerState := fun ⟨⟨i, j⟩, _⟩ ↦ j.val - i.val
  costBound := n
  h_cost := fun ⟨⟨_i, j⟩, _⟩ ↦ by
    dsimp
    have hj := j.isLt
    omega

/-- Local work bound: evaluating split points for state $(i, j)$ takes at most $n$ operations. -/
theorem matrixChain_costPerState_le (n : ℕ) (s : IntervalState n) :
    (matrixChainDP n).costPerState s ≤ n :=
  (matrixChainDP n).h_cost s

/-- Total operations across all states in the interval state space is bounded by $n^3$. -/
theorem matrixChainDP_totalCost_le (n : ℕ) :
    (matrixChainDP n).totalCost ≤ n ^ 3 := by
  have h1 := (matrixChainDP n).totalCost_le
  have h2 := card_intervalState_le n
  calc (matrixChainDP n).totalCost
    _ ≤ Fintype.card (IntervalState n) * (matrixChainDP n).costBound := h1
    _ = Fintype.card (IntervalState n) * n := rfl
    _ ≤ n ^ 2 * n := Nat.mul_le_mul_right n h2
    _ = n ^ 3 := by rw [← pow_succ]

/-- The total work evaluated against the exact triangular state count:
`totalCost ≤ (n * (n + 1) / 2) * n`. -/
theorem matrixChainDP_totalCost_le_triangular_mul (n : ℕ) :
    (matrixChainDP n).totalCost ≤ (n * (n + 1) / 2) * n := by
  have h1 := (matrixChainDP n).totalCost_le
  have h2 := card_intervalState n
  rw [h2] at h1
  exact h1

end Amort.DP
