# Insertion Sort

*Needs Binary GCD. Unlocks Merge Sort and Naive String Matching.*

This is the first chapter with lists, and the first one where writing the specification is the hard part. "The output is sorted" sounds like a complete description of sorting. It isn't, and seeing why is most of this chapter.

The companion file is `Tutorial/InsertionSort.lean`.

## 1. The problem

Given a list, return the same elements in non-decreasing order.

- `[5, 2, 4, 6, 1, 3]` becomes `[1, 2, 3, 4, 5, 6]`.
- Duplicates are kept: `[3, 1, 3]` becomes `[1, 3, 3]`.
- The empty list stays empty.

The examples use numbers compared with `≤`, but the repository sorts with any comparison you give it, as long as the comparison behaves like an ordering. Step 4 says exactly what that means.

## 2. What "correct" means in Lean

A correct output has to meet two conditions.

**It's sorted.** In Lean this is `List.Pairwise r out`: for every two elements of `out`, the earlier one and the later one satisfy `r`. For `[1, 2, 3]` with `≤`, that means 1 ≤ 2, 1 ≤ 3 and 2 ≤ 3.

**It's a rearrangement of the input.** In Lean this is `out ~ l`, which is short for `List.Perm out l`. It means the two lists contain the same elements, the same number of times each, possibly in a different order.

Each condition on its own is a broken specification:

- "Sorted" alone: a function that returns `[]` for every input passes, because an empty list is sorted.
- "Rearrangement" alone: a function that returns its input unchanged passes.
- "Sorted, and the same length as the input": a function that returns a list of zeros of the right length passes.

The companion file defines each of these broken functions and proves it passes its broken specification. We'll use them in "Spot the fake" below.

Some Lean for lists:

- `List α` is a list whose elements have type `α`. `α` is a type variable, like `T` in `List<T>`.
- `[]` is the empty list, and `a :: l` is the list with `a` in front of `l`. So `[1, 2]` is `1 :: 2 :: []`.
- `(· ≤ ·)` is shorthand for the function that takes `x` and `y` and returns `x ≤ y`.

## 3. The algorithm

Insertion sort builds the sorted output one element at a time, inserting each element into its place among the ones already sorted.

In Python:

```python
def ordered_insert(a, xs):
    if not xs: return [a]
    if a <= xs[0]: return [a] + xs
    return [xs[0]] + ordered_insert(a, xs[1:])

def insertion_sort(xs):
    if not xs: return []
    return ordered_insert(xs[0], insertion_sort(xs[1:]))
```

Notice the order: `insertion_sort` sorts the rest of the list first, then inserts the first element into it. So elements are inserted starting from the *end* of the input. That matters when we count comparisons.

The Lean versions are `List.orderedInsert` and `List.insertionSort`. They live in Mathlib rather than in this repository, so instead of sending you to Mathlib's source, the companion file states what they do and has Lean check each statement:

```lean
example (r : α → α → Prop) [DecidableRel r] (a : α) :
    List.orderedInsert r a [] = [a] := rfl

example (r : α → α → Prop) [DecidableRel r] (a b : α) (l : List α) :
    List.orderedInsert r a (b :: l) =
      if r a b then a :: b :: l else b :: List.orderedInsert r a l := rfl

example (r : α → α → Prop) [DecidableRel r] (a : α) (l : List α) :
    List.insertionSort r (a :: l) = List.orderedInsert r a (List.insertionSort r l) := rfl
```

These are the same three rules as the Python. The new pieces:

- `r : α → α → Prop` is the comparison: it takes two elements and returns a statement, such as `x ≤ y`. `Prop` is Lean's type of statements.
- `[DecidableRel r]` says the computer can actually work out whether `r a b` is true or false, which the `if` needs in order to run.
- `:= rfl` means the claim holds just by unfolding the definitions. Lean checks this, so these three lines are an accurate description of Mathlib's code, not a paraphrase.

Lean can see these functions stop without being told: every recursive call is on a shorter list.

## 4. The correctness theorems

The repository proves both halves of the specification, as two theorems. The file declares `α` and `r` once at the top:

```lean
variable {α : Type*} (r : α → α → Prop) [DecidableRel r]
```

so the theorems use them without listing them again.

```lean
theorem insertionSortWithCount_perm (l : List α) :
    (insertionSortWithCount r l).1 ~ l
```

```lean
theorem insertionSortWithCount_fst_sorted [Std.Total r] [IsTrans α r]
    (l : List α) : (insertionSortWithCount r l).1.Pairwise r
```

Both are about `(insertionSortWithCount r l).1`. That's the output of the step-counting version of insertion sort, which step 5 shows is exactly `List.insertionSort r l`.

The first theorem says the output is a rearrangement of the input. The second says it's sorted, and it has two extra conditions, both about the comparison `r`:

- `[Std.Total r]`: any two elements can be compared. For any `a` and `b`, either `r a b` or `r b a`.
- `[IsTrans α r]`: `r` is transitive. If `r a b` and `r b c`, then `r a c`.

These are fine conditions to have. They say `r` really is an ordering, and without them a sorted order might not even exist. What would *not* be fine is a condition about the output, such as assuming it's already sorted. The rearrangement theorem doesn't need either condition: moving elements around keeps them the same, however you compare them.

## 5. How many comparisons

We count comparisons: each time the code evaluates `r a b`. Here are the counting versions from `Amort/Sorting/InsertionSort.lean`:

```lean
def orderedInsertWithCount (a : α) : List α → List α × ℕ
  | [] => ([a], 0)
  | b :: l =>
    if r a b then
      (a :: b :: l, 1)
    else
      let res := orderedInsertWithCount a l
      (b :: res.1, 1 + res.2)
```

```lean
def insertionSortWithCount : List α → List α × ℕ
  | [] => ([], 0)
  | a :: l =>
    let res := insertionSortWithCount l
    let ins := orderedInsertWithCount r a res.1
    (ins.1, res.2 + ins.2)
```

The lines starting with `|` are *pattern matching*: one case for the empty list `[]` and one for a list `b :: l` with a first element `b`. It's Lean's version of `if not xs … else …`. Inserting into an empty list costs nothing. Otherwise, each comparison adds 1.

As before, one theorem says the counting version computes the real algorithm, and another bounds the count:

```lean
theorem insertionSortWithCount_fst (l : List α) :
    (insertionSortWithCount r l).1 = List.insertionSort r l
```

```lean
theorem insertionSortWithCount_snd_le_triangular (l : List α) :
    (insertionSortWithCount r l).2 ≤ l.length * (l.length - 1) / 2
```

For a list of length n, that's at most n(n − 1)/2 comparisons: 6 for four elements, 45 for ten. The worst case is when every insertion has to walk the whole sorted part. The best case is when every insertion stops at the first comparison, n − 1 in total:

```lean
#guard List.insertionSortWithCount (· ≤ ·) [5, 2, 4, 6, 1, 3] = ([1, 2, 3, 4, 5, 6], 13)
#guard List.insertionSortWithCount (· ≤ ·) [1, 2, 3, 4] = ([1, 2, 3, 4], 3)
#guard List.insertionSortWithCount (· ≤ ·) [4, 3, 2, 1] = ([1, 2, 3, 4], 6)
```

Why is `[1, 2, 3, 4]` the cheap one? Elements are inserted starting from the end, so each new element is smaller than everything sorted so far, and the first comparison already puts it in front. With `[4, 3, 2, 1]`, each new element is larger than everything sorted so far and has to walk past all of it.

## Spot the fake

### "sort is correct"

All three options compile; they're in the companion file.

**Option A**

```lean
def emptySort (_ : List ℕ) : List ℕ := []
```

```lean
theorem emptySort_sorted (l : List ℕ) : (emptySort l).Pairwise (· ≤ ·) := by
  simp [emptySort]
```

**Option B**

```lean
def zeroSort (l : List ℕ) : List ℕ := List.replicate l.length 0
```

```lean
theorem zeroSort_length_sorted (l : List ℕ) :
    (zeroSort l).length = l.length ∧ (zeroSort l).Pairwise (· ≤ ·) :=
```

**Option C**

```lean
theorem insertionSort_correct (l : List ℕ) :
    (List.insertionSortWithCount (· ≤ ·) l).1 ~ l ∧
    (List.insertionSortWithCount (· ≤ ·) l).1.Pairwise (· ≤ ·) :=
```

<details>
<summary>Show answer</summary>

C.

A and B are the broken specifications from step 2, applied to functions that obviously don't sort. `emptySort` throws the input away, and the output is sorted. `zeroSort` (`List.replicate n 0` is a list of `n` zeros) keeps the length and outputs zeros, which are sorted. Both theorems are true. They just don't say "this function sorts".

The only condition that rules out both is `~ l`, the output is a rearrangement of the input. When you read a claim that something "sorts", look for it.

</details>

## Exercises

**1. Predict.** What does `#eval List.insertionSortWithCount (· ≤ ·) [2, 1, 3]` print?

<details>
<summary>Show answer</summary>

`([1, 2, 3], 3)`. Working from the end: inserting 3 into `[]` costs nothing; inserting 1 into `[3]` takes one comparison (1 ≤ 3, so it goes in front); inserting 2 into `[1, 3]` takes two (2 ≤ 1 is false, then 2 ≤ 3 is true). That's 0 + 1 + 2 = 3.

</details>

**2. State it yourself.** Write a statement saying that sorting a list of natural numbers doesn't change its length.

<details>
<summary>Show answer</summary>

```lean
theorem insertionSort_length (l : List ℕ) :
    (List.insertionSortWithCount (· ≤ ·) l).1.length = l.length :=
```

The proof in the companion file is one line: a rearrangement always has the same length, so this follows from `insertionSortWithCount_perm`.

</details>

**3. Prove it with AI.** Sorting a list that's already sorted should give back the same list.

```lean
-- exercise
theorem insertionSort_of_sorted (l : List ℕ) (h : l.Pairwise (· ≤ ·)) :
    List.insertionSort (· ≤ ·) l = l := by
  sorry
```

Ask an assistant for a proof, then build. The condition `h` says the input is sorted. That's a condition on the input, and it's the whole point of the statement, so it belongs there. Mathlib may already contain this fact under another name; if the assistant finds it, that's a perfectly good proof.

## Lean introduced in this chapter

| You'll see | It means |
| :--- | :--- |
| `List α` | a list of elements of type `α` |
| `[]`, `a :: l` | the empty list; `a` in front of `l` |
| `\| [] => … \| b :: l => …` | pattern matching: one case per shape of list |
| `(· ≤ ·)` | the function `fun x y => x ≤ y` |
| `Prop` | the type of statements |
| `r : α → α → Prop` | a comparison between two elements |
| `[DecidableRel r]` | the computer can decide `r a b` |
| `[Std.Total r]`, `[IsTrans α r]` | `r` compares any two elements; `r` is transitive |
| `variable …` | declare names once for the rest of the file |
| `l.Pairwise r` | every earlier element relates to every later one by `r` |
| `l₁ ~ l₂` | `l₁` is a rearrangement of `l₂` (`List.Perm`) |
| `List.replicate n x` | a list of `n` copies of `x` |
| `l.length` | the number of elements in `l` |
