# Asymptotic Complexity Bridges for Data Structures

> **Status: stub — not verified** (Phase 3 canon stub; asymptotic theorems bound specification
> formulas awaiting instrumented execution implementations).


This document details the Lean 4 formalization of asymptotic complexity bounds connecting
concrete operational step counters for data structures to Mathlib's
`Mathlib.Analysis.Asymptotics.IsBigO` under `Filter.atTop` in `Amort.DataStructure.Asymptotics`.

---

## 1. Asymptotic Complexity Matrix

| Data Structure / Operation | Concrete Operational Bound | Mathlib `IsBigO` Bound | Bound Constant $C$ |
| :--- | :--- | :--- | :--- |
| **Linear Build-Heap** | $\le 2n$ | $O(n)$ | $C = 2$ |
| **Heapsort** | $\le 4n \cdot \text{Nat.size } n + 2$ | $O(n \log n)$ | $C = 4$ |
| **Online Running Median (Query)** | $= 1$ | $O(1)$ | $C = 1$ |
| **Online Running Median (Insert)** | $\le 6 \cdot \text{Nat.size } n$ | $O(\log n)$ | $C = 6$ |
| **Balanced BST (Insert / Rank)** | $\le (c + 2) \cdot \text{Nat.size } n$ | $O(\log n)$ | $C = c + 2$ |
| **Dynamic Array ($k$ Pushes)** | $\le 3k$ | $O(k)$ | $C = 3$ |
| **Two-Stack Queue ($m$ Ops)** | $\le 3m$ | $O(m)$ | $C = 3$ |

---

## 2. Key Theorems in `Amort.DataStructure.Asymptotics`

### Priority Queues & Heaps
```lean
theorem isBigO_buildHeap_atTop :
    (fun n ↦ ((buildHeapWork n (Nat.size n) : ℕ) : ℝ)) =O[Filter.atTop]
      (fun n ↦ ((n : ℕ) : ℝ))

theorem isBigO_heapsort_atTop :
    (fun n ↦ ((heapsortTotalWork n : ℕ) : ℝ)) =O[Filter.atTop]
      (fun n ↦ ((n * Nat.size n : ℕ) : ℝ))
```

### Online Running Median
```lean
theorem isBigO_medianQuery_atTop :
    (fun (_ : ℕ) ↦ ((medianQuerySteps : ℕ) : ℝ)) =O[Filter.atTop]
      (fun (_ : ℕ) ↦ (1 : ℝ))

theorem isBigO_onlineMedianInsert_atTop :
    (fun n ↦ ((onlineMedianInsertWork n : ℕ) : ℝ)) =O[Filter.atTop]
      (fun n ↦ ((Nat.size n : ℕ) : ℝ))
```

### Balanced Binary Search Trees
```lean
theorem isBigO_bbstInsertWork_atTop (c : ℕ) :
    (fun n ↦ ((insertWork n c : ℕ) : ℝ)) =O[Filter.atTop]
      (fun n ↦ ((Nat.size n : ℕ) : ℝ))
```

### Pure Amortized Classics
```lean
theorem isBigO_dynArrayTotalCost_atTop :
    (fun k ↦ ((3 * k : ℕ) : ℝ)) =O[Filter.atTop]
      (fun k ↦ ((k : ℕ) : ℝ))

theorem isBigO_twoStackQueueTotalCost_atTop :
    (fun m ↦ ((3 * m : ℕ) : ℝ)) =O[Filter.atTop]
      (fun m ↦ ((m : ℕ) : ℝ))
```
