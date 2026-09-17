# Algorithmic Recurrence and Complexity Theorems in Lean 4

This document details the Lean 4 formalization of algorithmic recurrence relations and
compositional complexity theorems in `Amort.Recurrence`, fully integrated with Mathlib's
`Mathlib.Analysis.Asymptotics.IsBigO` framework.

---

## 1. Architectural Overview

The recurrence formalization comprises five dedicated modules under `Amort/Recurrence/`:

```
Amort/
├── Amort.lean                  -- Root library export
├── GCD/                        -- Stein's Binary GCD & Euclidean GCD modules
├── Sorting/                    -- Insertion Sort, Merge Sort, and Lower Bounds
└── Recurrence/
    ├── Composition.lean        -- Compositional complexity algebra (nested loops & sequential phases)
    ├── Telescoping.lean        -- Linear & power telescoping recurrences (O(n^(k+1)), Insertion Sort)
    ├── Halving.lean            -- Halving recurrences (O(size n), O(log n))
    ├── BinarySearch.lean       -- Representative binary search step counter and logarithmic complexity
    ├── MasterTheorem.lean      -- Balanced divide-and-conquer master recurrence (O(n log n), Merge Sort)
    └── Recurrence.md           -- Architectural and mathematical documentation
```

All modules are exported by `Amort.lean` and compile with 0 warnings, 0 errors, and 0 `sorryAx`.

---

## 2. Compositional Complexity Algebra (`Composition.lean`)

Algorithmic time complexity analyses frequently combine subroutine bounds. We formalize
general composition rules for loop products, sequential phases, and asymptotic dominance.

### Mathematical Theorems

1. **Nested Loops (Product Rule)**:
   If an outer loop executes $N(n) = O(g_1(n))$ iterations and each iteration incurs
   cost $C(n) = O(g_2(n))$, the combined cost is $O(g_1(n) \cdot g_2(n))$:
   ```lean
   theorem isBigO_nested_loops (N g₁ C g₂ : α → ℝ)
       (hN : N =O[l] g₁) (hC : C =O[l] g₂) :
       (fun x ↦ N x * C x) =O[l] (fun x ↦ g₁ x * g₂ x)
   ```
   For pointwise bounded total cost $0 \le T(x) \le N(x) \cdot C(x)$:
   ```lean
   theorem isBigO_of_le_mul (T N g₁ C g₂ : α → ℝ) ... :
       T =O[l] (fun x ↦ g₁ x * g₂ x)
   ```

2. **Sequential Phases (Sum and Maximum Composition)**:
   Running phase 1 with $T_1(n) = O(g_1(n))$ followed by phase 2 with $T_2(n) = O(g_2(n))$:
   - Sum bound (nonnegative $g_1, g_2$):
     ```lean
     theorem isBigO_sequential_add (T₁ g₁ T₂ g₂ : α → ℝ) ... :
         (fun x ↦ T₁ x + T₂ x) =O[l] (fun x ↦ g₁ x + g₂ x)
     ```
   - Maximum bound:
     ```lean
     theorem isBigO_sequential_max (T₁ g₁ T₂ g₂ : α → ℝ)
         (hT₁ : T₁ =O[l] g₁) (hT₂ : T₂ =O[l] g₂) :
         (fun x ↦ T₁ x + T₂ x) =O[l] (fun x ↦ max |g₁ x| |g₂ x|)
     ```
   - Maximum phase cost $\max(T_1, T_2)$:
     ```lean
     theorem isBigO_max_of_max (T₁ g₁ T₂ g₂ : α → ℝ) ... :
         (fun x ↦ max (T₁ x) (T₂ x)) =O[l] (fun x ↦ max |g₁ x| |g₂ x|)
     ```

3. **Phase Dominance**:
   If phase 2 is asymptotically dominated by phase 1 ($g_2 = O(g_1)$):
   ```lean
   theorem isBigO_sequential_dominance (T₁ g₁ T₂ g₂ : α → ℝ)
       (hT₁ : T₁ =O[l] g₁) (hT₂ : T₂ =O[l] g₂) (hg : g₂ =O[l] g₁) :
       (fun x ↦ T₁ x + T₂ x) =O[l] g₁
   ```

4. **Natural Number Lifting**:
   `isBigO_nested_loops_nat`, `isBigO_of_le_mul_nat`, and `isBigO_sequential_add_nat`
   provide drop-in theorems for integer step counters coerced to $\mathbb{R}$.

---

## 3. Linear & Telescoping Recurrences (`Telescoping.lean`)

Loop algorithms commonly satisfy a step relation $T(n+1) \le T(n) + f(n)$.

### Mathematical Theorems

1. **Fundamental Telescoping Inequality**:
   ```lean
   theorem le_add_sum_range_of_step_le (h : ∀ i, T (i + 1) ≤ T i + f i) (n : ℕ) :
       T n ≤ T 0 + ∑ i ∈ range n, f i
   ```

2. **Constant Step Recurrences ($O(n)$)**:
   When $f(i) = c$:
   ```lean
   theorem telescoping_const_step_bound (c : ℕ) (h : ∀ i, T (i + 1) ≤ T i + c) (n : ℕ) :
       T n ≤ T 0 + c * n

   theorem telescoping_const_step_isBigO (c : ℕ) (h : ∀ i, T (i + 1) ≤ T i + c) :
       (fun n : ℕ ↦ ((T n : ℕ) : ℝ)) =O[Filter.atTop] (fun n : ℕ ↦ ((n : ℕ) : ℝ))
   ```

3. **General Power Step Recurrences ($O(n^{k+1})$)**:
   When $f(i) = c \cdot i^k$:
   ```lean
   theorem telescoping_power_step_bound (c k : ℕ)
       (h : ∀ i, T (i + 1) ≤ T i + c * i ^ k) (n : ℕ) :
       T n ≤ T 0 + c * n ^ (k + 1)

   theorem telescoping_power_step_isBigO (c k : ℕ)
       (h : ∀ i, T (i + 1) ≤ T i + c * i ^ k) :
       (fun n : ℕ ↦ ((T n : ℕ) : ℝ)) =O[Filter.atTop]
       (fun n : ℕ ↦ ((n ^ (k + 1) : ℕ) : ℝ))
   ```

4. **Linear Step & Quadratic Bound ($k=1 \implies O(n^2)$)**:
   Using $\sum_{i=0}^{n-1} i = n(n-1)/2 \le n^2$:
   ```lean
   theorem telescoping_linear_step_bound (c : ℕ)
       (h : ∀ i, T (i + 1) ≤ T i + c * i) (n : ℕ) :
       T n ≤ T 0 + c * n ^ 2

   theorem telescoping_linear_step_isBigO_sq (c : ℕ)
       (h : ∀ i, T (i + 1) ≤ T i + c * i) :
       (fun n : ℕ ↦ ((T n : ℕ) : ℝ)) =O[Filter.atTop]
       (fun n : ℕ ↦ ((n ^ 2 : ℕ) : ℝ))
   ```

5. **Application to Insertion Sort**:
   The exact recurrence `insertionSortRecBound 0 = 0`, `insertionSortRecBound (n + 1) = T(n) + n`
   satisfies the linear step condition with $c = 1, T(0) = 0$:
   - `insertionSortRecBound_le_sq`: `insertionSortRecBound n ≤ n ^ 2`
   - `insertionSortRecBound_isBigO_sq`: `insertionSortRecBound = O(n ^ 2)`
   - `insertionSortCount_le_recBound`: `List.insertionSortCount r l ≤ insertionSortRecBound l.length`

---

## 4. Halving & Binary Search Recurrences (`Halving.lean`, `BinarySearch.lean`)

Decrease-by-constant-factor algorithms satisfy $T(n) \le T(n/2) + c$ for $n \ge 2$.

### Mathematical Theorems

1. **Bit Size Halving Invariant**:
   Integer division by 2 decreases bit length by exactly 1:
   ```lean
   theorem size_div_two (n : ℕ) : Nat.size (n / 2) = Nat.size n - 1
   theorem size_ge_two_of_ge_two {n : ℕ} (h : 2 ≤ n) : 2 ≤ Nat.size n
   ```

2. **Concrete Halving Recurrence Bound**:
   By strong induction on $n$, each halving step consumes $c$ units of cost:
   ```lean
   theorem halving_recurrence_bound (T : ℕ → ℕ) (c : ℕ)
       (hrec : ∀ n, 2 ≤ n → T n ≤ T (n / 2) + c) (n : ℕ) (hn : 1 ≤ n) :
       T n ≤ c * Nat.size n + T 1

   theorem halving_recurrence_bound_all (T : ℕ → ℕ) (c : ℕ)
       (hrec : ∀ n, 2 ≤ n → T n ≤ T (n / 2) + c) (n : ℕ) :
       T n ≤ c * Nat.size n + T 0 + T 1
   ```

3. **Bit-Length and Natural Logarithm Dominance**:
   Using $2^{\text{size } n - 1} \le n < 2^{\text{size } n}$:
   ```lean
   theorem isBigO_size_log :
       (fun n : ℕ ↦ ((Nat.size n : ℕ) : ℝ)) =O[Filter.atTop]
       (fun n : ℕ ↦ Real.log (n : ℝ))
   ```

4. **Asymptotic Complexity**:
   ```lean
   theorem halving_recurrence_isBigO_size (T : ℕ → ℕ) (c : ℕ) ... :
       (fun n : ℕ ↦ ((T n : ℕ) : ℝ)) =O[Filter.atTop]
       (fun n : ℕ ↦ ((Nat.size n : ℕ) : ℝ))

   theorem halving_recurrence_isBigO_log (T : ℕ → ℕ) (c : ℕ) ... :
       (fun n : ℕ ↦ ((T n : ℕ) : ℝ)) =O[Filter.atTop]
       (fun n : ℕ ↦ Real.log (n : ℝ))
   ```

5. **Representative Binary Search**:
   Worst-case comparison step counter:
   ```lean
   def binarySearchSteps : ℕ → ℕ
     | 0 => 0
     | 1 => 1
     | n + 2 => 1 + binarySearchSteps ((n + 2) / 2)
   ```
   - `binarySearchSteps_step`: `binarySearchSteps n = binarySearchSteps (n / 2) + 1` for $n \ge 2$
   - `binarySearchSteps_le_halving`: Instantiates halving recurrence with $c = 1$
   - `binarySearchSteps_le_bound`: `binarySearchSteps n ≤ Nat.size n + 1`
   - `binarySearchSteps_le_size`: `binarySearchSteps n ≤ Nat.size n`
   - `binarySearchSteps_isBigO_size`: `binarySearchSteps = O(Nat.size n)`
   - `binarySearchSteps_isBigO_log`: `binarySearchSteps = O(log n)`

---

## 5. Balanced Divide-and-Conquer Master Recurrence (`MasterTheorem.lean`)

Balanced divide-and-conquer algorithms partition an input of size $n$ into subproblems
of size $\lceil n/2 \rceil = (n+1)/2$ and $\lfloor n/2 \rfloor = n/2$, combining them with linear work $c \cdot n$.

### Mathematical Theorems

1. **Dyadic Induction Lemma**:
   By induction on $k$, for any $n \le 2^k$:
   $$T(n) \le T(1) \cdot n + c \cdot n \cdot k$$
   ```lean
   theorem master_divide_conquer_aux (T : ℕ → ℕ) (c : ℕ)
       (hrec : ∀ n, 2 ≤ n → T n ≤ T ((n + 1) / 2) + T (n / 2) + c * n) :
       ∀ (k : ℕ) (n : ℕ), 1 ≤ n → n ≤ 2 ^ k → T n ≤ T 1 * n + c * n * k
   ```

2. **Concrete Bound**:
   Setting $k = \text{Nat.size } n$:
   ```lean
   theorem master_divide_conquer_bound (T : ℕ → ℕ) (c : ℕ)
       (hrec : ∀ n, 2 ≤ n → T n ≤ T ((n + 1) / 2) + T (n / 2) + c * n)
       (n : ℕ) (hn : 1 ≤ n) :
       T n ≤ (T 1 + c) * (n * Nat.size n)
   ```

3. **Asymptotic Complexity**:
   ```lean
   theorem master_divide_conquer_isBigO_mul_size (T : ℕ → ℕ) (c : ℕ) ... :
       (fun n : ℕ ↦ ((T n : ℕ) : ℝ)) =O[Filter.atTop]
       (fun n : ℕ ↦ ((n * Nat.size n : ℕ) : ℝ))

   theorem master_divide_conquer_isBigO_n_log_n (T : ℕ → ℕ) (c : ℕ) ... :
       (fun n : ℕ ↦ ((T n : ℕ) : ℝ)) =O[Filter.atTop]
       (fun n : ℕ ↦ (n : ℝ) * Real.log (n : ℝ))
   ```

4. **Application to Merge Sort**:
   The comparison recurrence `List.mergeSortRecBound` satisfies this recurrence with $c = 1$ and $T(1) = 0$:
   - `mergeSortRecBound_step`: `mergeSortRecBound n = mergeSortRecBound ((n+1)/2) + mergeSortRecBound (n/2) + n`
   - `mergeSortRecBound_le_rec`: satisfies the master recurrence
   - `mergeSortRecBound_le_mul_size_of_master`: `mergeSortRecBound n ≤ n * Nat.size n`
   - `mergeSortRecBound_isBigO_mul_size`: `mergeSortRecBound = O(n * Nat.size n)`
   - `mergeSortRecBound_isBigO_n_log_n`: `mergeSortRecBound = O(n log n)`
   - `mergeSortCount_le_master_bound`: `List.mergeSortCount le l ≤ l.length * Nat.size l.length`

---

## 6. Verification and Axiom Audit

All 54 theorems and lemmas across `Amort.Recurrence` have been audited via `#print axioms`.
Every declaration depends solely on foundational Lean 4 axioms:
- `propext` (Propositional Extensionality)
- `Classical.choice` (Axiom of Choice)
- `Quot.sound` (Quotient Soundness)

Zero theorems rely on `sorryAx`.
