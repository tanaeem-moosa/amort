# Binary Search

*Needs Binary GCD. Unlocks Merge Sort.*

Binary search is the first algorithm in the tree that only works if its input is prepared: the list must be sorted. So this is the first chapter where the theorem has a condition that genuinely belongs there. It's also the first one where the answer can be "not found", and where the correctness theorem is an "if and only if".

The companion file is `Tutorial/BinarySearch.lean`.

## 1. The problem

Given a sorted list and a target value, find a position where the target appears, or report that it isn't there.

- In `[1, 3, 5, 7, 9, 11]`, the target 7 is at index 3. Indices start at 0.
- The target 4 isn't in the list, so the answer is "not found".
- If the target appears more than once, any of its positions is a correct answer.

## 2. What "correct" means in Lean

A correct answer has two halves:

1. **Nothing wrong:** if the search returns an index, the target is at that index.
2. **Nothing missed:** if the target is in the list, the search finds it.

Either half alone is easy to fake. A search that always says "not found" never returns a wrong index. A search that always says "found, at 0" never misses anything. Spot the fake below uses both.

New Lean for this chapter:

- `Option ℕ` is the type of answers that may be missing. A value of this type is either `some i`, an actual index `i`, or `none`, meaning "not found". It plays the role of returning `None` or `-1` in other languages, except that Lean won't let you use the result as a number without first checking which case you're in.
- `xs[i]?` looks up index `i` in the list `xs` and returns an `Option`: `some x` if the index is valid and holds `x`, `none` if the index is out of range.
- `o.isSome` is true when `o` is `some _` and false when it's `none`.
- `x ∈ xs` means `x` is an element of `xs`.
- `P ↔ Q` means "`P` if and only if `Q`": each one implies the other.

## 3. The algorithm

Look at the middle element. If the target is smaller, search the left half; if larger, search the right half; if equal, you've found it. Each step throws away half of what's left.

In Python:

```python
def binary_search(xs, x):
    if not xs: return None
    mid = len(xs) // 2
    if x < xs[mid]: return binary_search(xs[:mid], x)
    if xs[mid] < x:
        r = binary_search(xs[mid + 1:], x)
        return None if r is None else r + mid + 1
    return mid
```

When the search goes right, the index it gets back is relative to the right half, so `mid + 1` has to be added back.

In Lean, from `Amort/Recurrence/BinarySearch.lean`. The file first declares the element type once:

```lean
variable {α : Type*} [LinearOrder α]
```

`[LinearOrder α]` says the elements can be compared with `<` and `≤` the usual way: any two elements are comparable, and the comparisons agree with each other. Then the search itself:

```lean
def binarySearch (xs : List α) (x : α) : Option ℕ :=
  if h : xs.length = 0 then
    none
  else
    let mid := xs.length / 2
    have hmid : mid < xs.length := by omega
    let midVal := xs[mid]
    if x < midVal then
      binarySearch (xs.take mid) x
    else if midVal < x then
      (binarySearch (xs.drop (mid + 1)) x).map (· + mid + 1)
    else
      some mid
termination_by xs.length
decreasing_by
  · simp only [List.length_take]; omega
  · simp only [List.length_drop]; omega
```

Here is how to read the Lean:

- `xs.take mid` is the first `mid` elements, like Python's `xs[:mid]`. `xs.drop (mid + 1)` is everything after position `mid`, like `xs[mid + 1:]`.
- `(…).map (· + mid + 1)` adds `mid + 1` to the answer if there is one, and leaves `none` alone. It's the Python line `None if r is None else r + mid + 1`.
- `have hmid : mid < xs.length := by omega` is a proof in the middle of the code. Lean only allows `xs[mid]` (no `?`) when it can see that `mid` is a valid index, so the code proves it right before the lookup. That's why there's no possibility of an index-out-of-range error: the bounds check happens once, at compile time.
- `termination_by xs.length` says the list gets shorter with every call, and the two lines after `decreasing_by` prove it, once for each recursive call.

### Running it

```lean
#guard binarySearch [1, 3, 5, 7, 9, 11] 7 = some 3
#guard binarySearch [1, 3, 5, 7, 9, 11] 4 = none
#guard binarySearch [2, 3, 1] 1 = none
```

The last line is the reason the list has to be sorted. 1 is in `[2, 3, 1]`, but the search looks at 3 in the middle, decides that 1 must be to the left, and never sees it.

## 4. The correctness theorems

The two halves from step 2 are two theorems. "Nothing wrong":

```lean
theorem binarySearch_some_get (xs : List α) (x : α) (i : ℕ) (h : binarySearch xs x = some i) :
    xs[i]? = some x
```

If the search returns `some i`, then looking up index `i` gives `x`. Notice there's no sortedness condition: even on an unsorted list, binary search never returns a wrong index. It just might miss.

And the "if and only if":

```lean
theorem binarySearch_isSome_iff (xs : List α) (x : α) (hsort : xs.Pairwise (· ≤ ·)) :
    (binarySearch xs x).isSome ↔ x ∈ xs
```

On a sorted list, the search finds something exactly when the target is in the list. The `→` direction is "nothing wrong" again, in weaker form. The `←` direction is "nothing missed", and it's the one that needs `hsort`.

`hsort : xs.Pairwise (· ≤ ·)` is the condition that the list is sorted, written the same way as in the Insertion Sort chapter. This is the kind of condition that belongs in a theorem: it's about the input, the algorithm really needs it, and the `[2, 3, 1]` example shows what goes wrong without it. Compare it with a condition that assumes part of the answer, like option B in Spot the fake below.

<details>
<summary>Show and explain the proofs (optional)</summary>

The "if and only if" is assembled from two lemmas, one per direction:

```lean
theorem binarySearch_isSome_iff (xs : List α) (x : α) (hsort : xs.Pairwise (· ≤ ·)) :
    (binarySearch xs x).isSome ↔ x ∈ xs :=
  ⟨fun h => by
    rcases Option.isSome_iff_exists.mp h with ⟨i, hi⟩
    exact binarySearch_mem xs x i hi,
   mem_imp_binarySearch_isSome xs x hsort⟩
```

- A proof of `P ↔ Q` is a pair `⟨proof of P → Q, proof of Q → P⟩`.
- A proof of `P → Q` is a function: `fun h => …` takes a proof `h` of `P` and builds a proof of `Q`.
- For `→`: `Option.isSome_iff_exists` turns "the result is `some` something" into "there is an `i` with result `some i`", and `rcases … with ⟨i, hi⟩` names that `i` and the fact `hi`. Then `binarySearch_mem` says the element at a returned index is in the list. It comes straight from `binarySearch_some_get`.
- For `←`: `mem_imp_binarySearch_isSome` does the real work, and it's where `hsort` is used.

That lemma is about sixty lines, but its core is one argument. Suppose `x` sits at index `k`, and the search compares it with the middle element and finds `x < xs[mid]`. The search goes left, so the proof must show `k < mid`:

```lean
        have h_k_lt_mid : k < mid := by
          by_contra! hge
          rcases hge.eq_or_lt with rfl | hgt
          · exact (lt_irrefl _) h1
          · have h_le := h_pw mid k hmid hk hgt
            exact not_lt.mpr h_le h1
```

- `by_contra! hge` is proof by contradiction: assume the opposite, `hge : mid ≤ k`, and derive something impossible.
- `rcases hge.eq_or_lt with rfl | hgt` splits `mid ≤ k` into `mid = k` or `mid < k`.
- If `mid = k`, then `h1` says `xs[k] < xs[k]`, and `lt_irrefl` says nothing is less than itself.
- If `mid < k`, then sortedness (`h_pw`, the `Pairwise` fact unpacked to indices) says `xs[mid] ≤ xs[k]`, which contradicts `h1 : xs[k] < xs[mid]`.

The rest of the lemma does the same for the right half, then shows that `x` is still in the half being searched and that the half is still sorted, and applies the induction hypothesis.

</details>

## 5. How many probes

We count *probes*: each look at a middle element. A probe compares the target with the middle element once or twice (`x < midVal`, then `midVal < x`), and it counts as one.

As in the earlier chapters, there's a counting version of the function, a theorem that it computes the same answer, and a bound:

```lean
theorem binarySearchWithCount_fst (xs : List α) (x : α) :
    (binarySearchWithCount xs x).1 = binarySearch xs x
```

```lean
theorem binarySearchWithCount_snd_le_size (xs : List α) (x : α) :
    (binarySearchWithCount xs x).2 ≤ Nat.size xs.length :=
```

The number of probes is at most the number of bits in the list's length. A list of a thousand elements needs at most 10 probes, because 1000 has 10 bits:

```lean
#guard binarySearchWithCount [1, 3, 5, 7, 9, 11] 7 = (some 3, 1)
#guard binarySearchWithCount [1, 3, 5, 7, 9, 11] 4 = (none, 3)
#guard binarySearchWithCount (List.range 1000) 1000 = (none, 9)
```

`List.range 1000` is the list `[0, 1, …, 999]`.

### What the count leaves out

The probe count is the number that matters for an array, where looking up the middle element takes one step. But this Lean function works on linked lists. On a linked list, `xs[mid]` walks `mid` steps from the front, and `take` and `drop` copy or walk half the list. So running this exact Lean function takes time proportional to the length of the list, not its logarithm. The file also has `binarySearchArray`, but it converts the array to a list first, so the same applies.

The theorem doesn't claim otherwise. It counts probes, and says so. This is the question from the Euclid chapter again: what exactly is being counted? Here the answer is "comparisons against the target", which is the standard measure for binary search, and it's honest. It just isn't running time.

<details>
<summary>Show and explain the proof (optional)</summary>

The bound goes through a separate step-counting formula:

```lean
theorem binarySearchWithCount_snd_le_size (xs : List α) (x : α) :
    (binarySearchWithCount xs x).2 ≤ Nat.size xs.length :=
  (binarySearchWithCount_snd_le_steps xs x).trans (binarySearchSteps_le_size xs.length)
```

`.trans` chains two inequalities: `a ≤ b` and `b ≤ c` give `a ≤ c`. The first says the real count is at most `binarySearchSteps xs.length`, the worst-case formula T(0) = 0, T(1) = 1, T(n) = 1 + T(n / 2). The second says the formula is at most the number of bits:

```lean
theorem binarySearchSteps_le_size (n : ℕ) :
    binarySearchSteps n ≤ Nat.size n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 =>
      rw [binarySearchSteps_zero]
      simp
    | 1 =>
      rw [binarySearchSteps_one]
      simp
    | n + 2 =>
      rw [binarySearchSteps]
      have hdiv_lt : (n + 2) / 2 < n + 2 := by omega
      have ih_div := ih ((n + 2) / 2) hdiv_lt
      have h_size : Nat.size ((n + 2) / 2) = Nat.size (n + 2) - 1 := size_div_two (n + 2)
      have h_size_ge : 2 ≤ Nat.size (n + 2) := size_ge_two_of_ge_two (by omega)
      omega
```

- Strong induction again, because the formula recurses on `n / 2`.
- `match n with | 0 => … | 1 => … | n + 2 => …` splits into the three cases of the formula's definition. `n + 2` is how Lean writes "a number that is at least 2".
- In the last case, the formula unfolds to `1 + binarySearchSteps ((n + 2) / 2)`. The induction hypothesis bounds that by the bits of `(n + 2) / 2`, and `h_size` says halving removes exactly one bit. `omega` adds it up.

`binarySearchWithCount_snd_le_steps`, the first link, is the longer proof. It follows the branches of `binarySearchWithCount`, and in the go-right branch it needs one extra fact: the formula only grows as `n` grows (`binarySearchSteps_mono`), because the right half can be one element shorter than `n / 2`.

</details>

## Spot the fake

### Round 1: "binary search is correct"

All options compile; the companion file has them, along with the two broken searches `neverFound` (always `none`) and `alwaysZero` (always `some 0`).

**Option A**

```lean
theorem binarySearch_some_get (xs : List α) (x : α) (i : ℕ) (h : binarySearch xs x = some i) :
    xs[i]? = some x
```

**Option B**

```lean
theorem binarySearch_isSome_iff_of_mem (xs : List ℕ) (x : ℕ) (_hsort : xs.Pairwise (· ≤ ·))
    (hx : x ∈ xs) : (binarySearch xs x).isSome ↔ x ∈ xs :=
```

**Option C**

```lean
theorem binarySearch_some_get (xs : List α) (x : α) (i : ℕ) (h : binarySearch xs x = some i) :
    xs[i]? = some x
```

```lean
theorem binarySearch_isSome_iff (xs : List α) (x : α) (hsort : xs.Pairwise (· ≤ ·)) :
    (binarySearch xs x).isSome ↔ x ∈ xs
```

<details>
<summary>Show answer</summary>

C.

A is only "nothing wrong". `neverFound` passes it, because when there's never a result, there's never a wrong one. The companion file proves `neverFound_some_get`.

B looks like the real "if and only if", but the extra condition `hx : x ∈ xs` assumes the target is in the list. Under that assumption the right side of `↔` is simply true, so the statement only says "the search finds something". It says nothing about targets that aren't there. `alwaysZero` passes it (`alwaysZero_isSome_iff_of_mem`). Unlike `hsort`, `hx` isn't a fact about the input that the algorithm needs. It's half of the answer, moved into the assumptions.

C has both halves: the index is right, and the search finds the target exactly when it's there. Even C only says the search finds *some* position, not the first one. For duplicates, that's what we asked for in step 1.

</details>

### Round 2: "binary search makes at most bits(n) probes"

**Option A**

```lean
theorem binarySearchSteps_le_size (n : ℕ) :
    binarySearchSteps n ≤ Nat.size n := by
```

**Option B**

```lean
theorem binarySearchWithCount_fst (xs : List α) (x : α) :
    (binarySearchWithCount xs x).1 = binarySearch xs x
```

```lean
theorem binarySearchWithCount_snd_le_size (xs : List α) (x : α) :
    (binarySearchWithCount xs x).2 ≤ Nat.size xs.length :=
```

**Option C**

```lean
theorem binarySearchWithCount_snd_le_length (xs : List ℕ) (x : ℕ) :
    (binarySearchWithCount xs x).2 ≤ xs.length :=
```

<details>
<summary>Show answer</summary>

B.

A is a real theorem from the reference file, and it's even used in the proof of B. But on its own it's about `binarySearchSteps`, a formula: T(n) = 1 + T(n / 2). Nothing in A connects that formula to the search function. A formula that someone believes describes the algorithm isn't the algorithm. The connection is `binarySearchWithCount_snd_le_steps`, which is proved separately.

C is about the real counter and it's true, but it's a linear bound: up to a thousand probes for a thousand elements, rather than 10.

</details>

## Exercises

**1. Predict.** What does `#eval binarySearchWithCount [1, 3, 5, 7, 9, 11] 1` print?

<details>
<summary>Show answer</summary>

`(some 0, 3)`. The first probe looks at index 3 (the value 7) and goes left to `[1, 3, 5]`. The second looks at 3 and goes left to `[1]`. The third finds 1 at index 0.

</details>

**2. State it yourself.** Write a statement saying that an index returned by binary search is always less than the list's length.

<details>
<summary>Show answer</summary>

```lean
theorem binarySearch_lt_length (xs : List ℕ) (x i : ℕ) (h : binarySearch xs x = some i) :
    i < xs.length := by
```

No sortedness condition is needed, just as for `binarySearch_some_get`, which the companion file's proof uses: if `xs[i]?` is `some x`, then `i` must be a valid index.

</details>

**3. Prove it with AI.**

```lean
-- exercise
theorem binarySearch_nil (x : ℕ) : binarySearch ([] : List ℕ) x = none := by
  sorry
```

`([] : List ℕ)` is the empty list, with its type written out so Lean knows what kind of list it is. Paste the statement at the end of the companion file, ask an assistant for a proof, and build.

## Lean introduced in this chapter

| You'll see | It means |
| :--- | :--- |
| `Option ℕ` | a number that may be missing |
| `some i`, `none` | an actual value; no value |
| `o.isSome` | `o` is `some _` |
| `o.map f` | apply `f` inside `some`; leave `none` alone |
| `xs[i]?` | the element at index `i`, as an `Option` |
| `xs[i]` | the element at index `i`; Lean must see a proof that `i` is in range |
| `x ∈ xs` | `x` is an element of `xs` |
| `P ↔ Q` | `P` if and only if `Q` |
| `xs.take n`, `xs.drop n` | the first `n` elements; everything after the first `n` |
| `[LinearOrder α]` | elements of `α` compare with `<` and `≤` the usual way |
| `List.range n` | the list `[0, 1, …, n − 1]` |

## Proof tactics in this chapter (optional)

New ones from the "Show and explain the proof" sections.

| You'll see | It means |
| :--- | :--- |
| `⟨p, q⟩` for `P ↔ Q` | a proof of each direction |
| `fun h => …` | a proof of `P → Q`: given `h : P`, build a proof of `Q` |
| `rcases h with ⟨i, hi⟩` | unpack "there is an `i` with `hi`" |
| `by_contra! h` | proof by contradiction, assuming the opposite as `h` |
| `lt_irrefl` | nothing is less than itself |
| `match n with \| 0 => … \| n + 2 => …` | split on the shape of a number |
| `h₁.trans h₂` | chain `a ≤ b` and `b ≤ c` into `a ≤ c` |
