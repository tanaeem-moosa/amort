# 🗂️ Insertion Sort

> **Skill Tree Tier 2 | Sorting & Searching**  
> **Prerequisites:** Binary GCD (`BGCD`)  
> **Unlocks:** Merge Sort (`MERGE`), Naive String Matching (`NAIVE`)  
> **Companion Lean File:** `Tutorial/InsertionSort.lean`  
> **Reference Module:** `Amort.Sorting.InsertionSort`  
> **Headline Theorems:** `List.insertionSortWithCount_fst`, `List.insertionSortWithCount_perm`, `List.insertionSortWithCount_fst_sorted`, `List.insertionSortWithCount_snd_le_triangular`, `List.insertionSortWithCount_snd_le_sq`, `List.isBigO_insertionSortWithCount_snd_atTop`

---

## The Big Idea

Sorting is the quintessential problem in computer science. Yet in formal verification, it holds a famous trap:

> **It is surprisingly easy to prove that a completely broken sorting algorithm is "correct".**

If your specification merely says: *"no adjacent element in the output is out of order"*, then a function that discards the input and returns the empty list `[]` is **provably correct**!

In this chapter, we master the **two-part sorting specification**:
1. **Conservation:** The output is a permutation of the input ($\sim$).
2. **Orderedness:** The output satisfies pairwise ordering (`List.Pairwise`).

We also formalize the classic quadratic comparison recurrence ($T(n) \le T(n-1) + (n-1)$) and prove the concrete triangular bound $\frac{n(n-1)}{2} \le n^2$.

---

## Step 1: Define the Problem

Given a list $l$ of elements of type $\alpha$ and a total ordering relation $r$ (such as $\le$), rearrange the elements into non-decreasing order according to $r$.

### Concrete Examples
- Sorting `[5, 2, 4, 6, 1, 3]` with respect to $\le$ yields `[1, 2, 3, 4, 5, 6]`.
- Sorting `[4, 3, 2, 1]` yields `[1, 2, 3, 4]`.
- Sorting an already sorted list `[1, 2, 3, 4]` returns `[1, 2, 3, 4]`.

### Edge Cases
1. **Empty list `[]`:** Vacuously sorted.
2. **Single-element list `[x]`:** Trivial base case.
3. **Duplicates `[3, 1, 3]`:** Must preserve multiplicities (output `[1, 3, 3]`).

---

## Step 2: Formalize the Definition

What does it mean for a list `out` to be a valid sort of `inp`? A genuine specification requires **two independent conditions**:

### 1. Conservation (`List.Perm` / `~`)
The output must contain the exact same elements as the input, with the exact same multiplicities:
$$\text{out} \sim \text{inp} \quad (\text{written in Lean as } \text{out.Perm inp})$$

### 2. Orderedness (`List.Pairwise`)
Every pair of elements in the output must respect the ordering relation $r$:
$$\text{List.Pairwise } r \text{ out}$$
For example, `List.Pairwise (· ≤ ·) [1, 2, 3]` means:
$$1 \le 2 \quad \land \quad 1 \le 3 \quad \land \quad 2 \le 3$$

### Why One Condition Alone Is a Fake Specification
- **Sortedness alone:** A function `def emptySort (_ : List ℕ) := []` provably satisfies `(emptySort l).Pairwise (· ≤ ·)`. It is sorted, but drops all data!
- **Permutation alone:** A function `def identitySort (l : List ℕ) := l` provably satisfies `identitySort l ~ l`. It preserves all elements, but performs zero sorting!
- **Length + Sortedness:** A function returning `[0, 0, 0, 0]` for any 4-element list preserves length and is sorted, but destroys the values.

A genuine sorting specification must enforce both:
```lean
(sort l) ~ l ∧ (sort l).Pairwise r
```

---

## Step 3: Understand the Algorithm

Insertion sort processes elements one by one, inserting each new element into its proper position within the already sorted prefix.

### Lean 4 Implementation
In Lean 4, insertion sort is defined via two structurally recursive functions:

```lean
-- Insert element `a` into an already-sorted list:
def orderedInsert (a : α) : List α → List α
  | [] => [a]
  | b :: l => if r a b then a :: b :: l else b :: orderedInsert a l

-- Sort the list by recursively sorting the tail, then inserting the head:
def insertionSort : List α → List α
  | [] => []
  | a :: l => orderedInsert a (insertionSort l)
```

### Running the Algorithm in Lean

Open `Tutorial/InsertionSort.lean` and execute `#eval`:

```lean
-- Sorting with comparison counts:
#eval List.insertionSortWithCount (· ≤ ·) [5, 2, 4, 6, 1, 3]
-- Output: ([1, 2, 3, 4, 5, 6], 13)

-- Best case: already sorted input (n - 1 comparisons):
#eval List.insertionSortWithCount (· ≤ ·) [1, 2, 3, 4]
-- Output: ([1, 2, 3, 4], 3)

-- Worst case: reverse sorted input (n * (n - 1) / 2 comparisons):
#eval List.insertionSortWithCount (· ≤ ·) [4, 3, 2, 1]
-- Output: ([1, 2, 3, 4], 6)
```

### Termination Proof
Lean proves termination automatically by **structural induction on lists**:
- `orderedInsert a l` recurses on the tail `l`.
- `insertionSort (a :: l)` recurses on `l`.
Both calls strictly shrink the list length.

---

## Step 4: State Correctness

In `Amort/Sorting/InsertionSort.lean`, both halves of the specification are formally proven:

### Theorem 1: Permutation Preservation
```lean
theorem insertionSortWithCount_perm (r : α → α → Prop) [DecidableRel r] (l : List α) :
    (insertionSortWithCount r l).1 ~ l
```

### Theorem 2: Pairwise Sortedness
```lean
theorem insertionSortWithCount_fst_sorted (r : α → α → Prop) [DecidableRel r] [Std.Total r] [IsTrans α r] (l : List α) :
    (insertionSortWithCount r l).1.Pairwise r
```

### Mathematical Hypotheses Explained
Notice the typeclasses required for sortedness:
- `[DecidableRel r]`: The relation $r(a, b)$ can be evaluated by a computer (returns `true` or `false`).
- `[Std.Total r]`: The relation is total: for any two elements $a$ and $b$, either $r(a, b)$ or $r(b, a)$ holds.
- `[IsTrans α r]`: The relation is transitive: $r(a, b) \land r(b, c) \implies r(a, c)$.

Without transitivity and totality, sorting is mathematically undefined!

---

## Step 5: State Time Complexity

What are we counting in Insertion Sort? We count **element comparisons** (`r a b`).

### The Instrumented Function and Coupling
```lean
def insertionSortWithCount : List α → List α × ℕ := ...
```
Returns `(sorted_list, comparison_count)`. The coupling theorems verify:
```lean
theorem insertionSortWithCount_fst (l : List α) :
    (insertionSortWithCount r l).1 = List.insertionSort r l

theorem insertionSortWithCount_snd (l : List α) :
    (insertionSortWithCount r l).2 = List.insertionSortCount r l
```

### The Triangular Comparison Upper Bound
When inserting element $k$ into a sorted list of length $k - 1$, we make at most $k - 1$ comparisons (`orderedInsertCount_le`). Summing over all $n$ elements yields the classic triangular recurrence:
$$T(n) \le T(n - 1) + (n - 1) \implies T(n) \le \sum_{i=0}^{n-1} i = \frac{n(n - 1)}{2}$$

The headline theorem proves this exact inequality in Lean:

```lean
theorem insertionSortWithCount_snd_le_triangular (l : List α) :
    (insertionSortWithCount r l).2 ≤ l.length * (l.length - 1) / 2
```

And its quadratic relaxation:
```lean
theorem insertionSortWithCount_snd_le_sq (l : List α) :
    (insertionSortWithCount r l).2 ≤ l.length ^ 2
```

### Asymptotic Complexity in Mathlib
In `Amort/Sorting/Asymptotics.lean`, this bound is connected to Mathlib's `Asymptotics.IsBigO`:
```lean
theorem isBigO_insertionSortWithCount_snd_atTop :
    (fun l : List α ↦ ((insertionSortWithCount r l).2 : ℝ)) =O[Filter.atTop]
    (fun l : List α ↦ ((l.length : ℝ) ^ 2))
```

---

## 🎯 Spot the Fake

An AI agent claims to have formalized a verified sorting algorithm. Which specification genuinely proves that the algorithm sorts the input list?

### Statement A (Sortedness Only / Empty-List Fake)
```lean
theorem sort_correct (xs : List ℕ) :
    (sort xs).Pairwise (· ≤ ·)
```
> **Verdict: FAKE.**  
> An algorithm defined as `def sort (_ : List ℕ) := []` provably satisfies this statement! Dropping all elements trivially eliminates all out-of-order pairs.

### Statement B (Sortedness + Length / Value-Erasing Fake)
```lean
theorem sort_correct (xs : List ℕ) :
    (sort xs).length = xs.length ∧ (sort xs).Pairwise (· ≤ ·)
```
> **Verdict: FAKE.**  
> An algorithm defined as `def sort xs := List.replicate xs.length 0` preserves length and is sorted (`[0, 0, 0, 0]` is sorted), but destroys all original input values!

### Statement C (Permutation + Sortedness)
```lean
theorem sort_correct (xs : List ℕ) :
    (sort xs).Perm xs ∧ (sort xs).Pairwise (· ≤ ·)
```
> **Verdict: GENUINE.**  
> Demanding both `Perm xs` (multiset conservation) and `Pairwise (· ≤ ·)` (sortedness) completely characterizes a correct sorting algorithm.

---

## 🧪 Interactive Exercises

### 1. Predict
1. **Question 1:** Given input `[4, 2, 7, 1]`, what does `#eval (insertionSortWithCount (· ≤ ·) [4, 2, 7, 1]).1` evaluate to?
   - *Expected Answer:* `[1, 2, 4, 7]`
2. **Question 2:** How many comparisons are performed when sorting the reverse-ordered list `[4, 3, 2, 1]`?
   - *Expected Answer:* `6`
   - *Formula:* $\frac{4 \cdot (4 - 1)}{2} = \frac{12}{2} = 6$.
3. **Question 3:** How many comparisons are performed on the already-sorted list `[1, 2, 3, 4]`?
   - *Expected Answer:* `3` (each insertion checks the first element and stops immediately: $n - 1$).

### 2. State It Yourself
In `Tutorial/InsertionSort.lean`, verify that sorting preserves list length:

```lean
/-- Sorting preserves list length -/
example (l : List ℕ) : (List.insertionSortWithCount (· ≤ ·) l).1.length = l.length := by
  exact (List.insertionSortWithCount_perm (· ≤ ·) l).length_eq
```

### 3. Prove It with AI
Copy this theorem into an AI chat:
```lean
theorem empty_list_is_sorted : ([ ] : List ℕ).Pairwise (· ≤ ·)
```
Ask: *"Prove that the empty list is pairwise sorted in Lean 4."*  
Notice that the proof is simply `by simp`. This illustrates why the sortedness condition alone is never sufficient!
