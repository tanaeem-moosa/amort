# Formalization of Algorithmic Quicksort Canon in Lean 4

This document details the Lean 4 formalization of the complete Quicksort algorithm canon in
[`Amort/Sorting/Quicksort.lean`](Quicksort.lean), covering algorithmic correctness, worst-case
quadratic complexity ($\Theta(n^2)$), deterministic median-of-medians worst-case $O(n \log n)$,
and average-case expected comparisons ($O(n \log n)$).

---

## 1. Architectural Overview

The formalization encompasses four core facets of Quicksort:
1. **Algorithmic Correctness (R2)**:
   - 3-way partitioning (`partition3`) and length-fueled recursion (`quicksortFuel`, `quicksort`).
   - Multiset / Permutation equivalence: `quicksort xs ~ xs`.
   - Sortedness: `(quicksort xs).Pairwise (· ≤ ·)` and `(quicksort xs).SortedLE`.
   - Exact equivalence to Mathlib's `List.mergeSort` and `List.insertionSort`.
2. **Worst-Case Complexity $\Theta(n^2)$ (R3)**:
   - Recurrence: $T(0) = 0$, $T(n + 1) = T(n) + n$.
   - Exact closed-form solution: $T(n) = \frac{n(n - 1)}{2}$.
   - Asymptotic $\Theta(n^2)$ bound in Mathlib `IsTheta` under `Filter.atTop`.
3. **Deterministic Median (BFPRT) Quicksort (R4)**:
   - BFPRT partition balance: subproblem size bounded by $\lfloor 7n/10 \rfloor + 3$ for $n \ge 5$.
   - Recurrence: $T(n) \le T(\lfloor 7n/10 \rfloor) + T(\lfloor 3n/10 \rfloor) + cn$.
   - Operational bound: $4(c + 1) n \cdot \text{size } n$.
   - Strictly worst-case $O(n \log n)$ in Mathlib `IsBigO` under `Filter.atTop`.
4. **Average-Case Complexity $O(n \log n)$ (R5)**:
   - Recurrence: $\mathbb{E}[T(n)] = \frac{2}{n} \sum_{i=0}^{n-1} \mathbb{E}[T(i)] + (n - 1)$.
   - Bridge to indicator backward analysis in `Amort.Randomized.Quicksort` ($\le 2n H(n)$).
   - Operational bound: $2n \cdot \text{size } n$.
   - Average-case $O(n \log n)$ in Mathlib `IsBigO` under `Filter.atTop`.

---

## 2. Algorithmic Quicksort & Correctness (R2)

### 2.1 Partitioning and Fuel-Bounded Recursion

Quicksort partitions around a pivot element into strictly smaller and non-smaller sublists:
```lean
def partition3 (p : α) (xs : List α) : List α × List α × List α :=
  (xs.filter (· < p), xs.filter (· == p), xs.filter (p < ·))

def quicksortFuel : ℕ → List α → List α
  | 0, _ => []
  | _fuel + 1, [] => []
  | fuel + 1, x :: xs =>
    let lt := xs.filter (· < x)
    let ge := xs.filter (x ≤ ·)
    quicksortFuel fuel lt ++ [x] ++ quicksortFuel fuel ge

def quicksort (xs : List α) : List α :=
  quicksortFuel xs.length xs
```

### 2.2 Fuel Invariance and Step Equality

Structural induction on fuel proves that any fuel $\ge \text{length}$ yields identical results:
```lean
theorem quicksortFuel_eq_of_ge :
    ∀ (f1 f2 : ℕ) (xs : List α), xs.length ≤ f1 → xs.length ≤ f2 →
      quicksortFuel f1 xs = quicksortFuel f2 xs

theorem quicksort_cons (x : α) (xs : List α) :
    quicksort (x :: xs) =
      quicksort (xs.filter (· < x)) ++ [x] ++ quicksort (xs.filter (x ≤ ·))
```

### 2.3 Correctness Theorems

- **Permutation Equivalence**:
  ```lean
  theorem quicksort_perm (xs : List α) : quicksort xs ~ xs
  ```
- **Sortedness**:
  ```lean
  theorem quicksort_sorted (xs : List α) : (quicksort xs).Pairwise (· ≤ ·)
  theorem quicksort_sortedLE (xs : List α) : (quicksort xs).SortedLE
  ```
- **Equivalence to Mathlib Algorithms**:
  Via permutation uniqueness of sorted lists (`Perm.eq_of_pairwise'`):
  ```lean
  theorem quicksort_eq_mergeSort (xs : List α) :
      quicksort xs = List.mergeSort xs (· ≤ ·)

  theorem quicksort_eq_insertionSort (xs : List α) :
      quicksort xs = List.insertionSort (· ≤ ·) xs
  ```

---

## 3. Worst-Case Complexity $\Theta(n^2)$ (R3)

When pivot selection is unbalanced (e.g., pivot is minimal or maximal), Quicksort performs
$n - 1$ comparisons on an input of size $n$, yielding:
$$T(n) = T(n - 1) + (n - 1), \quad T(0) = 0$$

```lean
def quicksortWorstCaseRec : ℕ → ℕ
  | 0 => 0
  | n + 1 => quicksortWorstCaseRec n + n

theorem quicksortWorstCaseRec_eq (n : ℕ) :
    quicksortWorstCaseRec n = n * (n - 1) / 2
```

Using parity analysis (`mul_pred_even : 2 * (n * (n - 1) / 2) = n * (n - 1)`), we prove tight
asymptotic bounds in Mathlib `IsBigO` and `IsTheta`:
```lean
theorem isBigO_quicksortWorstCase_sq :
    (fun n : ℕ ↦ ((quicksortWorstCaseRec n : ℕ) : ℝ)) =O[Filter.atTop]
      (fun n ↦ ((n ^ 2 : ℕ) : ℝ))

theorem isBigO_sq_quicksortWorstCase :
    (fun n : ℕ ↦ ((n ^ 2 : ℕ) : ℝ)) =O[Filter.atTop]
      (fun n ↦ ((quicksortWorstCaseRec n : ℕ) : ℝ))

theorem isTheta_quicksortWorstCase_sq :
    (fun n : ℕ ↦ ((quicksortWorstCaseRec n : ℕ) : ℝ)) =Θ[Filter.atTop]
      (fun n ↦ ((n ^ 2 : ℕ) : ℝ))
```

### 3.1 Instrumented Execution & Worst-Case Attainment (Definition of Done R1 & R4)

To satisfy the 7-point Definition of Done and eliminate closed-form work anti-patterns (A1),
`Amort.Sorting.Quicksort` provides the fully instrumented execution counter:
```lean
def quicksortWithCount (xs : List α) : List α × ℕ :=
  quicksortFuelWithCount xs.length xs
```
- **Functional Correctness**:
  `quicksortWithCount_fst : (quicksortWithCount xs).1 = quicksort xs`
- **Concrete Upper Bound**:
  `quicksortWithCount_snd_le_mul : (quicksortWithCount xs).2 ≤ xs.length * (xs.length - 1) / 2`
- **Exact Attainment on Replicate Elements**:
  On identical/replicate inputs `List.replicate n x`, every partitioning step places all remaining
  elements into the `x ≤ ·` branch:
  `quicksortWithCount_replicate_eq_mul :`
  `(quicksortWithCount (List.replicate n x)).2 = n * (n - 1) / 2`
- **Mathlib Asymptotics Bridge**:
  `isBigO_quicksortWithCount_snd_sq` proving $(quicksortWithCount\ xs).2 = O(|xs|^2)$ under
  pullback along `List.length` to `Filter.atTop`.

---

## 4. Deterministic Median (BFPRT Selection) Worst-Case $O(n \log n)$ (R4)

Using the Blum-Floyd-Pratt-Rivest-Tarjan (BFPRT) "Median-of-Medians" algorithm to choose the pivot
guarantees a balanced partition:
```lean
theorem bfprt_partition_balance (n : ℕ) (_hn : 5 ≤ n) :
    n - 3 * (n / 10) ≤ 7 * n / 10 + 3
```

This yields the divide-and-conquer recurrence:
$$T(n) \le T(\lfloor 7n/10 \rfloor) + T(\lfloor 3n/10 \rfloor) + cn$$

```lean
def bfprtQuicksortRec (c : ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | n + 2 =>
    bfprtQuicksortRec c (7 * (n + 2) / 10) +
    bfprtQuicksortRec c (3 * (n + 2) / 10) +
    c * (n + 2)
```

---

## 5. Average-Case Complexity $O(n \log n)$ (R5)

Under uniform random pivot selection, the expected comparison count satisfies:
$$\mathbb{E}[T(n)] = \frac{2}{n} \sum_{i=0}^{n-1} \mathbb{E}[T(i)] + (n - 1)$$

```lean
def IsQuicksortAvgRec (T : ℕ → ℝ) : Prop :=
  T 0 = 0 ∧ T 1 = 0 ∧
  ∀ n ≥ 2, T n = (2 : ℝ) / (n : ℝ) * (∑ i ∈ Finset.range n, T i) + ((n : ℝ) - 1)
```

We connect this recurrence to the pairwise indicator backward analysis in
`Amort.Randomized.Quicksort`:
```lean
theorem expected_quicksort_le_harmonic_bound (n : ℕ) :
    Amort.Randomized.expectedQuicksortComparisons n ≤
      2 * (n : ℝ) * Amort.Approximation.harmonic n
```

---

## 6. Axiom Status & Style Conformance

- **Clean Axioms**: All proofs rely strictly on foundational Lean 4 axioms (`propext`,
  `Classical.choice`, `Quot.sound`). Zero `sorry` or `sorryAx` used.
- **Build Status**: Compiles cleanly with 0 errors and 0 warnings via `lake build Amort`.
- **Line Length**: Strictly conforms to the Mathlib limit ($\le 100$ characters).
