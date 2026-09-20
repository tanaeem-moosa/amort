# Formalization of Sorting Complexity: Upper Bounds ($O(n^2)$, $O(n \log n)$) and Information-Theoretic Lower Bound ($\Omega(n \log n)$)

This document details the Lean 4 formalization of comparison counting, mathematical correctness,
concrete upper bounds, decision tree models, permutation coverage, and asymptotic time complexity
for comparison-based sorting algorithms in the `Amort.Sorting` namespace, integrating with Mathlib's
`Mathlib.Analysis.Asymptotics.IsBigO` framework.

---

## 1. Architectural Overview

The sorting complexity formalization comprises six dedicated modules under `Amort/Sorting/`:

```
Amort/
├── Amort.lean                  -- Root library export
├── GCD/                        -- Stein's Binary GCD & Euclidean GCD modules
└── Sorting/
    ├── InsertionSort.lean      -- Comparison counting, instrumented sort, triangular & O(n²) bounds
    ├── MergeSort.lean          -- Merge comparison counting, D&C recurrence, O(n * size n) bounds
    ├── Quicksort.lean          -- Algorithmic quicksort canon, Θ(n²), BFPRT, avg O(n log n)
    ├── Asymptotics.lean        -- Asymptotic bridges connecting concrete bounds to Mathlib IsBigO
    ├── DecisionTree.lean       -- Abstract binary decision trees, depth, leaf count bound (R1)
    ├── LowerBound.lean         -- Permutation coverage, clog bound, and Ω(n log n) asymptotics (R2, R3)
    ├── Quicksort.md            -- Dedicated Quicksort architecture and complexity documentation
    └── Sorting.md              -- Architectural and mathematical documentation
```

All modules are exported by `Amort.lean`.

---

## 2. Insertion Sort: Comparison Counting & $O(n^2)$ Bound (R1)

### Mathematical Model

Mathlib defines insertion sort (`List.insertionSort`) via right fold with `List.orderedInsert`:
```lean
def orderedInsert (a : α) : List α → List α
  | [] => [a]
  | b :: l => if a ≼ b then a :: b :: l else b :: orderedInsert a l

def insertionSort : List α → List α := foldr (orderedInsert r) []
```

We formalize comparison counting with two complementary representations:
1. **Direct Counters**:
   - `orderedInsertCount (r : α → α → Prop) [DecidableRel r] (a : α) : List α → ℕ`:
     Counts comparisons when inserting `a` into a list. In the base case `[]`, 0 comparisons
     are made; in the inductive case `b :: l`, 1 comparison is made between `a` and `b`, and
     if `¬ r a b`, insertion continues recursively into `l`.
   - `insertionSortCount (r : α → α → Prop) [DecidableRel r] : List α → ℕ`:
     Counts the total comparisons performed across all insertions:
     `insertionSortCount r (a :: l) = orderedInsertCount r a (insertionSort r l) + insertionSortCount r l`.

2. **Instrumented Representations**:
   - `orderedInsertWithCount (r : α → α → Prop) [DecidableRel r] (a : α) : List α → List α × ℕ`
   - `insertionSortWithCount (r : α → α → Prop) [DecidableRel r] : List α → List α × ℕ`

### Equivalence to Mathlib

We prove that the instrumented sorting functions compute the exact sorted output of Mathlib's
`List.insertionSort` and track the exact counts of `List.insertionSortCount`:
- `orderedInsertWithCount_fst`: `(orderedInsertWithCount r a l).1 = List.orderedInsert r a l`
- `orderedInsertWithCount_snd`: `(orderedInsertWithCount r a l).2 = orderedInsertCount r a l`
- `insertionSortWithCount_fst`: `(insertionSortWithCount r l).1 = List.insertionSort r l`
- `insertionSortWithCount_snd`: `(insertionSortWithCount r l).2 = insertionSortCount r l`

### Concrete Comparison Upper Bounds

1. **Single-Insertion Bound**:
   `orderedInsertCount_le`: Inserting into a list of length $k$ requires at most $k$ comparisons:
   $$\text{orderedInsertCount } r\ a\ l \le l.\text{length}$$

2. **Triangular Number Bound**:
   By Mathlib's `List.length_insertionSort`, sorting preserves list length:
   $$(\text{insertionSort } r\ l).\text{length} = l.\text{length}$$
   Therefore, inserting the $(k+1)$-th element into the sorted prefix of length $k$ takes at most $k$ comparisons.
   Summing over $k = 0, 1, \dots, n-1$:
   $$\sum_{k=0}^{n-1} k = \frac{n(n-1)}{2}$$
   In `Amort/Sorting/InsertionSort.lean`, this is formalized as:
   ```lean
   theorem insertionSortCount_le_triangular (l : List α) :
       insertionSortCount r l ≤ l.length * (l.length - 1) / 2
   ```

3. **Quadratic Bound via Telescoping Recurrence**:
   In addition to the triangular number bound, insertion sort directly maps to the general
   linear telescoping recurrence in `Amort.Recurrence.Telescoping` ($T(n+1) \le T(n) + n$):
   ```lean
   theorem insertionSortCount_le_recBound (l : List α) :
       insertionSortCount r l ≤ insertionSortRecBound l.length

   theorem insertionSortRecBound_le_sq (n : ℕ) :
       insertionSortRecBound n ≤ n ^ 2

   theorem insertionSortCount_le_sq (l : List α) :
       insertionSortCount r l ≤ l.length ^ 2
   ```
   and for instrumented sort:
   ```lean
   theorem insertionSortWithCount_snd_le_sq (l : List α) :
       (insertionSortWithCount r l).2 ≤ l.length ^ 2
   ```

---

## 3. Merge Sort: Comparison Counting & $O(n \log n)$ Bound (R2)

### Mathematical Model

Lean core / Mathlib defines `List.merge` and `List.mergeSort`:
- `merge xs ys le`: Merges two sorted lists by comparing heads `le x y`.
- `mergeSort xs le`: Recursively splits `xs` via `splitInTwo` into contiguous sublists of lengths
  $(n+1)/2$ and $n/2$, sorts each recursively, and merges the results.

We define:
1. `mergeCount le xs ys`: Exact comparisons performed during merging.
2. `mergeWithCount le xs ys`: Instrumented merge returning `(merged_list, comparisons)`.
3. `mergeSortCount le xs`: Exact comparisons performed by merge sort.
4. `mergeSortWithCount le xs`: Instrumented merge sort returning `(sorted_list, comparisons)`.
5. `mergeSortRecBound (n : ℕ) : ℕ`:
   $$T(0) = 0, \quad T(1) = 0, \quad T(n+2) = T((n+3)/2) + T((n+2)/2) + (n+2)$$

### Equivalence to Mathlib & Core

We formally prove:
- `mergeWithCount_fst`: `(mergeWithCount le xs ys).1 = merge xs ys le`
- `mergeWithCount_snd`: `(mergeWithCount le xs ys).2 = mergeCount le xs ys`
- `mergeSortWithCount_fst`: `(mergeSortWithCount le xs).1 = mergeSort xs le`
- `mergeSortWithCount_snd`: `(mergeSortWithCount le xs).2 = mergeSortCount le xs`
- `mergeSortWithCount_fst_eq_insertionSort`: For total, transitive, antisymmetric relations,
  `(mergeSortWithCount (r · ·) xs).1 = insertionSort r xs`, connecting directly to
  Mathlib's `mergeSort_eq_insertionSort`.

### Concrete Comparison Upper Bounds

1. **Merge Step Bound**:
   In each comparison between `x :: xs` and `y :: ys`, at least one element is emitted to the output.
   Thus:
   ```lean
   theorem mergeCount_le (le : α → α → Bool) (xs ys : List α) :
       mergeCount le xs ys ≤ xs.length + ys.length
   ```

2. **Reduction to Divide-and-Conquer Recurrence**:
   Since `(mergeSort lr.1.1 le).length = lr.1.1.length` by `List.length_mergeSort`, the merge step
   takes at most $\text{length}(lr.1.1) + \text{length}(lr.2.1) = xs.\text{length}$ comparisons.
   Therefore, by well-founded structural induction:
   ```lean
   lemma mergeSortCount_le_recBound (le : α → α → Bool) (xs : List α) :
       mergeSortCount le xs ≤ mergeSortRecBound xs.length
   ```

3. **Power-of-Two Bounding Lemma via Master Theorem**:
   In `Amort/Sorting/MergeSort.lean`, `mergeSortRecBound` is shown to satisfy the balanced
   divide-and-conquer master recurrence with $c = 1$ (`mergeSortRecBound_le_rec`), and directly
   derives its dyadic power-of-two bound via `Amort.Recurrence.master_divide_conquer_aux`:
   ```lean
   theorem mergeSortRecBound_le_mul_of_le_two_pow :
       ∀ (k : ℕ) (n : ℕ), n ≤ 2 ^ k → mergeSortRecBound n ≤ n * k
   ```

4. **Bit-Size Upper Bound**:
   By Mathlib's `Nat.lt_size_self`, $n < 2^{\text{Nat.size } n}$, so $n \le 2^{\text{Nat.size } n}$.
   Instantiating $k = \text{Nat.size } n$:
   ```lean
   theorem mergeSortRecBound_le_mul_size (n : ℕ) :
       mergeSortRecBound n ≤ n * Nat.size n

   theorem mergeSortCount_le_mul_size (le : α → α → Bool) (xs : List α) :
       mergeSortCount le xs ≤ xs.length * Nat.size xs.length

   theorem mergeSortWithCount_snd_le_mul_size (le : α → α → Bool) (xs : List α) :
       (mergeSortWithCount le xs).2 ≤ xs.length * Nat.size xs.length
   ```

---

## 4. Asymptotics Bridge to Mathlib `IsBigO` (R1, R2)

In `Amort/Sorting/Asymptotics.lean`, concrete comparison bounds are connected to Mathlib's
`Mathlib.Analysis.Asymptotics.IsBigO` framework.

### Universal Filter Bounds
Because both bounds hold pointwise with constant $c = 1$:
$$\text{insertionSortCount } r\ l \le 1 \cdot l.\text{length}^2$$
$$\text{mergeSortCount } le\ l \le 1 \cdot (l.\text{length} \cdot \text{Nat.size } l.\text{length})$$
the asymptotic relation holds with respect to *any* filter $F$ on `List α`:
- `isBigO_insertionSortCount_sq (F : Filter (List α))`
- `isBigO_mergeSortCount_mul_size (le : α → α → Bool) (F : Filter (List α))`

### Pullback Filter under `List.length` towards `Filter.atTop`
Specializing $F$ to `Filter.comap List.length Filter.atTop` yields asymptotic theorems as
input list length grows to infinity:
```lean
theorem isBigO_insertionSortCount_atTop :
    (fun l : List α ↦ ((insertionSortCount r l : ℕ) : ℝ)) =O[
      Filter.comap List.length Filter.atTop]
    (fun l : List α ↦ ((l.length ^ 2 : ℕ) : ℝ))

theorem isBigO_insertionSortWithCount_snd_atTop :
    (fun l : List α ↦ (((insertionSortWithCount r l).2 : ℕ) : ℝ)) =O[
      Filter.comap List.length Filter.atTop]
    (fun l : List α ↦ ((l.length ^ 2 : ℕ) : ℝ))

theorem isBigO_mergeSortCount_atTop (le : α → α → Bool) :
    (fun l : List α ↦ ((mergeSortCount le l : ℕ) : ℝ)) =O[
      Filter.comap List.length Filter.atTop]
    (fun l : List α ↦ ((l.length * Nat.size l.length : ℕ) : ℝ))

theorem isBigO_mergeSortWithCount_snd_atTop (le : α → α → Bool) :
    (fun l : List α ↦ (((mergeSortWithCount le l).2 : ℕ) : ℝ)) =O[
      Filter.comap List.length Filter.atTop]
    (fun l : List α ↦ ((l.length * Nat.size l.length : ℕ) : ℝ))
```

### Arithmetic Recurrence Asymptotics on `ℕ`
Directly on natural numbers under `Filter.atTop`:
```lean
theorem isBigO_insertionSort_triangular_atTop :
    (fun n : ℕ ↦ ((n * (n - 1) / 2 : ℕ) : ℝ)) =O[Filter.atTop]
    (fun n : ℕ ↦ ((n ^ 2 : ℕ) : ℝ))

theorem isBigO_mergeSortRecBound_atTop :
    (fun n : ℕ ↦ ((mergeSortRecBound n : ℕ) : ℝ)) =O[Filter.atTop]
    (fun n : ℕ ↦ ((n * Nat.size n : ℕ) : ℝ))
```

---

## 5. Decision Tree Model: Depth & Leaf Count (R1)

In `Amort/Sorting/DecisionTree.lean`, comparison-based algorithms are modeled as abstract binary
decision trees:

```lean
inductive DecisionTree (α : Type u) (β : Type v) where
  | leaf (val : β) : DecisionTree α β
  | node (query : α) (left right : DecisionTree α β) : DecisionTree α β
```

### Depth and Leaf Count
- `depth : DecisionTree α β → ℕ`:
  - `depth (leaf _) = 0`
  - `depth (node _ left right) = max (depth left) (depth right) + 1`
- `leafCount : DecisionTree α β → ℕ`:
  - `leafCount (leaf _) = 1`
  - `leafCount (node _ left right) = leafCount left + leafCount right`

### Structural Induction Bound
By structural induction on `T`, any binary decision tree of depth `d` has at most $2^d$ leaves:
```lean
theorem leafCount_le_two_pow_depth (T : DecisionTree α β) :
    leafCount T ≤ 2 ^ depth T
```

### Evaluation & Leaf Sets
- `eval (T : DecisionTree α β) (oracle : α → Bool) : β`: Evaluates the tree against an oracle.
- `leavesList (T : DecisionTree α β) : List β`: Multiset of all leaf values.
- `leaves [DecidableEq β] (T : DecisionTree α β) : Finset β`: Finset of distinct leaf values.
- `eval_mem_leavesList`: Every execution reaches a leaf in `leavesList T`.
- `card_leaves_le_leafCount`: Distinct leaves cardinality is bounded by `leafCount T`.
- `card_leaves_le_two_pow_depth`:
  $$\text{card}(\text{leaves } T) \le \text{leafCount } T \le 2^{\text{depth } T}$$

---

## 6. Permutation Coverage & Factorial Lower Bound (R2)

In `Amort/Sorting/LowerBound.lean`, sorting algorithms on $n$ elements are evaluated on inputs
represented by permutations of `Fin n`.

### Permutation Oracle
For each permutation $\sigma \in \text{Equiv.Perm } (\text{Fin } n)$ and query pair $(i, j)$:
```lean
def permOracle (σ : Equiv.Perm (Fin n)) (q : Fin n × Fin n) : Bool :=
  decide (σ q.1 ≤ σ q.2)
```

### Correctness Condition
An algorithm distinguishing all $n!$ input orderings has an injective evaluation map:
```lean
def DistinguishesPermutations {β : Type*} (T : DecisionTree (Fin n × Fin n) β) : Prop :=
  Function.Injective (fun σ : Equiv.Perm (Fin n) ↦ DecisionTree.eval T (permOracle σ))
```
Any sorting tree that outputs $\sigma^{-1}$ (`IsSortingTree T`) satisfies this condition:
```lean
theorem distinguishesPermutations_of_isSortingTree
    (T : DecisionTree (Fin n × Fin n) (Equiv.Perm (Fin n))) (hT : IsSortingTree T) :
    DistinguishesPermutations T
```

### Reachable Leaves and Factorial Bounds
Since the evaluation map $\sigma \mapsto \text{eval } T\ (\text{permOracle } \sigma)$ is injective
and its image is contained in $\text{leaves } T$:
```lean
theorem factorial_le_card_leaves [DecidableEq β] (T : DecisionTree (Fin n × Fin n) β)
    (hT : DistinguishesPermutations T) :
    Nat.factorial n ≤ (DecisionTree.leaves T).card

theorem factorial_le_leafCount (T : DecisionTree (Fin n × Fin n) β)
    (hT : DistinguishesPermutations T) :
    Nat.factorial n ≤ DecisionTree.leafCount T

theorem factorial_le_two_pow_depth (T : DecisionTree (Fin n × Fin n) β)
    (hT : DistinguishesPermutations T) :
    Nat.factorial n ≤ 2 ^ DecisionTree.depth T
```

### Worst-Case Query Lower Bound
Taking binary ceiling logarithm gives the fundamental comparison lower bound:
```lean
theorem clog_factorial_le_depth (T : DecisionTree (Fin n × Fin n) β)
    (hT : DistinguishesPermutations T) :
    Nat.clog 2 (Nat.factorial n) ≤ DecisionTree.depth T
```

---

## 7. Factorial Combinatorial & Asymptotic Bounds ($\Omega(n \log n)$) (R3)

### Combinatorial Lower Bound on Factorial Growth
By pairing factors in $n! = \prod_{i=1}^n i$, the top half $i \ge \lfloor n/2 \rfloor + 1$
each contribute at least $n/2 + 1 > n/2$. Formalized via Mathlib's `factorial_mul_pow_le_factorial`:
```lean
lemma pow_div_two_le_factorial (n : ℕ) :
    (n / 2) ^ (n / 2) ≤ Nat.factorial n
```

Auxiliary quadratic and linear lemmas establish that for $n \ge 6$:
- `nat_div_two_sq_ge (n : ℕ) (hn : 6 ≤ n) : n ≤ (n / 2) ^ 2`
- `nat_le_three_mul_div_two (n : ℕ) (hn : 2 ≤ n) : n ≤ 3 * (n / 2)`

Consequently, for $n \ge 6$:
$$n \log n \le 3(n/2) \cdot (2 \log(n/2)) = 6 (n/2) \log(n/2) \le 6 \log(n!)$$

### Asymptotic Equivalence to Mathlib `IsBigO` / `IsTheta`
Under `Filter.atTop`, $n \log n = O(\log(n!))$:
```lean
theorem isBigO_n_log_n_factorial :
    (fun n : ℕ ↦ (n : ℝ) * Real.log (n : ℝ)) =O[Filter.atTop]
    (fun n : ℕ ↦ Real.log ((Nat.factorial n : ℕ) : ℝ))
```

Combined with the upper bound $n! \le n^n$ (`Nat.factorial_le_pow`):
```lean
theorem isBigO_factorial_n_log_n :
    (fun n : ℕ ↦ Real.log ((Nat.factorial n : ℕ) : ℝ)) =O[Filter.atTop]
    (fun n : ℕ ↦ (n : ℝ) * Real.log (n : ℝ))

theorem isTheta_factorial_n_log_n :
    (fun n : ℕ ↦ Real.log ((Nat.factorial n : ℕ) : ℝ)) =Θ[Filter.atTop]
    (fun n : ℕ ↦ (n : ℝ) * Real.log (n : ℝ))
```

### Depth Lower Bound Asymptotics
Connecting $\log(n!)$ to $\text{Nat.clog } 2 (n!)$ and decision tree depth:
```lean
theorem isBigO_log_factorial_clog_factorial :
    (fun n : ℕ ↦ Real.log ((Nat.factorial n : ℕ) : ℝ)) =O[Filter.atTop]
    (fun n : ℕ ↦ ((Nat.clog 2 (Nat.factorial n) : ℕ) : ℝ))

theorem isBigO_n_log_n_clog_factorial :
    (fun n : ℕ ↦ (n : ℝ) * Real.log (n : ℝ)) =O[Filter.atTop]
    (fun n : ℕ ↦ ((Nat.clog 2 (Nat.factorial n) : ℕ) : ℝ))

theorem isBigO_n_log_n_depth {β : (n : ℕ) → Type*}
    (T : (n : ℕ) → DecisionTree (Fin n × Fin n) (β n))
    (hT : ∀ n, DistinguishesPermutations (T n)) :
    (fun n : ℕ ↦ (n : ℝ) * Real.log (n : ℝ)) =O[Filter.atTop]
    (fun n : ℕ ↦ (((T n).depth : ℕ) : ℝ))
```

---

---

## 8. Quicksort Algorithm Canon: Correctness, $\Theta(n^2)$, BFPRT, and Average-Case (R2-R5)

Module `Amort.Sorting.Quicksort` formalizes the complete algorithmic Quicksort canon:

### 8.1 Partitioning & Algorithmic Correctness (R2)
- **Length-Fueled Recursion**: `quicksortFuel` and `quicksort` avoid well-founded termination
  issues and elaborate cleanly.
- **Invariance & Step Equality**: `quicksortFuel_eq_of_ge` and `quicksort_cons`.
- **Permutation Equivalence**: `quicksort_perm` proves `∀ xs, quicksort xs ~ xs`.
- **Sortedness**: `quicksort_sorted` proves `∀ xs, (quicksort xs).Pairwise (· ≤ ·)`, and
  `quicksort_sortedLE` establishes `List.SortedLE`.
- **Equivalence to Mathlib**: `quicksort_eq_mergeSort` and `quicksort_eq_insertionSort` prove
  exact equality with Mathlib's sorting algorithms via `Perm.eq_of_pairwise'`.

### 8.2 Worst-Case Quadratic Complexity ($\Theta(n^2)$) (R3)
- **Recurrence**: $T(n+1) = T(n) + n$ with $T(0) = 0$ (`quicksortWorstCaseRec`).
- **Exact Closed Form**: `quicksortWorstCaseRec_eq` establishes $T(n) = n(n - 1) / 2$.
- **Asymptotic Tight Bound**: `isBigO_quicksortWorstCase_sq` ($O(n^2)$) and
  `isBigO_sq_quicksortWorstCase` ($\Omega(n^2)$) combine to yield
  `isTheta_quicksortWorstCase_sq` ($\Theta(n^2)$) under `Filter.atTop`.

### 8.3 Deterministic Median (BFPRT) Worst-Case $O(n \log n)$ (R4)
- **Partition Invariant**: `bfprt_partition_balance` proves subproblems
  $\le \lfloor 7n/10 \rfloor + 3$.
- **Divide-and-Conquer Recurrence**:
  $T(n) \le T(\lfloor 7n/10 \rfloor) + T(\lfloor 3n/10 \rfloor) + cn$.
- **Worst-Case Asymptotics**: `isBigO_bfprtQuicksort_n_log_n` establishes worst-case $O(n \log n)$.

### 8.4 Average-Case Expected Complexity ($O(n \log n)$) (R5)
- **Expected Recurrence**: `IsQuicksortAvgRec` characterizes
  $\mathbb{E}[T(n)] = \frac{2}{n}\sum \mathbb{E}[T(i)] + (n - 1)$.
- **Harmonic Bound**: `expected_quicksort_le_harmonic_bound` bridges to
  `Amort.Randomized.Quicksort`.
- **Average-Case Asymptotics**: `isBigO_quicksortAvg_n_log_n` establishes expected $O(n \log n)$.

---

## 9. Axiom Integrity Verification

All definitions, auxiliary lemmas, and main theorems adhere strictly to standard foundational
axioms. `#print axioms` confirms zero reliance on `sorryAx`:

| Declaration | Axioms Used | Status |
| :--- | :--- | :--- |
| `List.insertionSortCount_le_triangular` | `[propext, Classical.choice, Quot.sound]` | Clean |
| `List.insertionSortCount_le_sq` | `[propext, Classical.choice, Quot.sound]` | Clean |
| `List.insertionSortWithCount_fst` | `[propext]` | Clean |
| `List.insertionSortWithCount_snd` | `[propext, Quot.sound]` | Clean |
| `List.mergeSortCount_le_mul_size` | `[propext, Classical.choice, Quot.sound]` | Clean |
| `List.mergeSortWithCount_fst` | `[propext, Classical.choice, Quot.sound]` | Clean |
| `List.mergeSortWithCount_snd` | `[propext, Classical.choice, Quot.sound]` | Clean |
| `List.mergeSortWithCount_fst_eq_insertionSort` | `[propext, Classical.choice, Quot.sound]` | Clean |
| `List.isBigO_insertionSortCount_sq` | `[propext, Classical.choice, Quot.sound]` | Clean |
| `List.isBigO_insertionSortCount_atTop` | `[propext, Classical.choice, Quot.sound]` | Clean |
| `List.isBigO_insertionSortWithCount_snd_atTop` | `[propext, Classical.choice, Quot.sound]` | Clean |
| `List.isBigO_insertionSort_triangular_atTop` | `[propext, Classical.choice, Quot.sound]` | Clean |
| `List.isBigO_mergeSortCount_mul_size` | `[propext, Classical.choice, Quot.sound]` | Clean |
| `List.isBigO_mergeSortCount_atTop` | `[propext, Classical.choice, Quot.sound]` | Clean |
| `List.isBigO_mergeSortWithCount_snd_atTop` | `[propext, Classical.choice, Quot.sound]` | Clean |
| `List.isBigO_mergeSortRecBound_atTop` | `[propext, Classical.choice, Quot.sound]` | Clean |
| `DecisionTree.leafCount_le_two_pow_depth` | `[propext]` | Clean |
| `DecisionTree.card_leaves_le_two_pow_depth` | `[propext, Classical.choice, Quot.sound]` | Clean |
| `distinguishesPermutations_of_isSortingTree` | `[propext, Classical.choice, Quot.sound]` | Clean |
| `factorial_le_card_leaves` | `[propext, Classical.choice, Quot.sound]` | Clean |
| `factorial_le_leafCount` | `[propext, Classical.choice, Quot.sound]` | Clean |
| `factorial_le_two_pow_depth` | `[propext, Classical.choice, Quot.sound]` | Clean |
| `clog_factorial_le_depth` | `[propext, Classical.choice, Quot.sound]` | Clean |
| `pow_div_two_le_factorial` | `[propext, Quot.sound]` | Clean |
| `isBigO_n_log_n_factorial` | `[propext, Classical.choice, Quot.sound]` | Clean |
| `isBigO_factorial_n_log_n` | `[propext, Classical.choice, Quot.sound]` | Clean |
| `isTheta_factorial_n_log_n` | `[propext, Classical.choice, Quot.sound]` | Clean |
| `isBigO_log_factorial_clog_factorial` | `[propext, Classical.choice, Quot.sound]` | Clean |
| `isBigO_n_log_n_clog_factorial` | `[propext, Classical.choice, Quot.sound]` | Clean |
| `isBigO_n_log_n_depth` | `[propext, Classical.choice, Quot.sound]` | Clean |
| `quicksort_perm` | `[propext, Quot.sound]` | Clean |
| `quicksort_sorted` | `[propext, Quot.sound]` | Clean |
| `quicksort_sortedLE` | `[propext, Classical.choice, Quot.sound]` | Clean |
| `quicksort_eq_mergeSort` | `[propext, Quot.sound]` | Clean |
| `quicksort_eq_insertionSort` | `[propext, Classical.choice, Quot.sound]` | Clean |
| `quicksortWorstCaseRec_eq` | `[propext, Quot.sound]` | Clean |
| `isBigO_quicksortWorstCase_sq` | `[propext, Classical.choice, Quot.sound]` | Clean |
| `isBigO_sq_quicksortWorstCase` | `[propext, Classical.choice, Quot.sound]` | Clean |
| `isTheta_quicksortWorstCase_sq` | `[propext, Classical.choice, Quot.sound]` | Clean |
| `bfprt_partition_balance` | `[propext, Quot.sound]` | Clean |
| `bfprtQuicksortRec_step` | `[propext, Classical.choice, Quot.sound]` | Clean |
| `isBigO_bfprtQuicksort_mul_size` | `[propext, Classical.choice, Quot.sound]` | Clean |
| `isBigO_bfprtQuicksort_n_log_n` | `[propext, Classical.choice, Quot.sound]` | Clean |
| `expected_quicksort_le_harmonic_bound` | `[propext, Classical.choice, Quot.sound]` | Clean |
| `isBigO_quicksortAvg_mul_size` | `[propext, Classical.choice, Quot.sound]` | Clean |
| `isBigO_quicksortAvg_n_log_n` | `[propext, Classical.choice, Quot.sound]` | Clean |

---

## 10. Style & Linter Conformance

- **Namespacing**: Scoped under `namespace Amort.Sorting` (and `List` for list sorting algorithms).
- **Classification**: `lemma` for auxiliaries, `theorem` for milestones.
- **Documentation**: All public definitions and theorems documented with docstrings `/-- ... -/`.
- **Line Length**: All lines across all Lean source files $\le 100$ characters.
- **Build Status**: `lake build` succeeds with 0 errors and 0 warnings (2136 jobs).
