# Dynamic Array

*Needs Binary GCD. Unlocks Two-Stack Queue and Binary Heap.*

A dynamic array (Python's `list`, C++'s `vector`, Java's `ArrayList`) is an array that grows when it fills up. Most pushes are cheap, but now and then one push copies the entire array. This chapter is about the claim everyone repeats, "push is O(1) amortized", and what it takes to state it precisely. The word "amortized" is where this repository's name comes from.

The companion file is `Tutorial/DynamicArray.lean`.

## 1. The problem

A dynamic array keeps its elements in a block of memory with room for `capacity` elements, of which `size` are in use. To push a new element:

- If there's room (`size < capacity`), write the element into the next free slot. Cost: 1.
- If the block is full (`size = capacity`), allocate a new block twice as big, copy all `size` elements across, then write the new one. Cost: `size + 1`.

A single push can therefore cost as much as the whole array. The claim to pin down is that this doesn't matter on average: any sequence of `k` pushes, starting from an empty array, costs at most `3k` in total.

## 2. What "correct" means in Lean

This chapter is different from the earlier ones, and it's worth being upfront about how. The repository models a dynamic array by its two numbers only, `size` and `capacity`. It doesn't store any elements. That's enough to analyze the cost, because the cost depends only on those two numbers. But it means there's no theorem here saying the elements end up in the right places. When you read a theorem, what the model leaves out is part of what the theorem says.

So "correct" here means two facts about the numbers: after `k` pushes there are `k` more elements, and `size` never exceeds `capacity`. The main theorem is the cost bound.

The model is a *structure*, Lean's version of a record or a class with only fields:

```lean
structure DynArrayState where
  size : ℕ
  capacity : ℕ
  deriving Repr, DecidableEq
```

- If `s : DynArrayState`, then `s.size` and `s.capacity` are its fields.
- `⟨0, 1⟩` builds a value from its fields in order: size 0, capacity 1. The array we'll start from, `DynArrayState.initOne`, is exactly that.
- `deriving Repr, DecidableEq` asks Lean to generate code to print values and to compare them with `=`. That's what lets `#eval` and `#guard` work on them.

## 3. The algorithm

In Python, tracking only the two numbers, as the model does:

```python
def push_cost(size, capacity):
    return 1 if size < capacity else size + 1

def push_state(size, capacity):
    return (size + 1, capacity if size < capacity else 2 * capacity)
```

In Lean, from `Amort/DataStructure/DynamicArray.lean`:

```lean
def pushState (s : DynArrayState) : DynArrayState :=
  if s.size < s.capacity then
    ⟨s.size + 1, s.capacity⟩
  else
    ⟨s.size + 1, 2 * s.capacity⟩
```

```lean
def pushActualCost (s : DynArrayState) : ℕ :=
  if s.size < s.capacity then 1
  else s.size + 1
```

These are the two rules from step 1, word for word. The cost model is a definition too, so it's something to check: copying `size` elements costs `size`, and writing the new one costs 1. That's the standard model, and it's honest.

To talk about many pushes, the file defines the state after `k` pushes, and the total cost of those `k` pushes:

```lean
def pushSeq : ℕ → DynArrayState → DynArrayState
  | 0, s => s
  | k + 1, s => pushState (pushSeq k s)
```

```lean
def pushSeqCost : ℕ → DynArrayState → ℕ
  | 0, _ => 0
  | k + 1, s => pushSeqCost k s + pushActualCost (pushSeq k s)
```

Both are defined by pattern matching on the number of pushes. Zero pushes leave the state alone and cost nothing. `k + 1` pushes are `k` pushes followed by one more. `_` means an argument the case doesn't use.

### Running it

Starting from an empty array with capacity 1, here are the costs of the first nine pushes, and the state after them:

```lean
#guard (List.range 9).map (fun k => pushActualCost (pushSeq k DynArrayState.initOne)) =
  [1, 2, 3, 1, 5, 1, 1, 1, 9]
```

```lean
#guard pushSeq 9 DynArrayState.initOne = ⟨9, 16⟩
```

The expensive pushes are the 2nd, 3rd, 5th and 9th: the ones that find the array full at sizes 1, 2, 4 and 8. Between them, the cheap pushes get further and further apart.

## 4. The correctness theorems

```lean
theorem pushSeq_size (k : ℕ) (s : DynArrayState) :
    (pushSeq k s).size = s.size + k := by
```

```lean
theorem pushSeq_size_le_capacity_initOne (k : ℕ) :
    (pushSeq k DynArrayState.initOne).size ≤ (pushSeq k DynArrayState.initOne).capacity :=
```

Each push adds exactly one element, and starting from `initOne`, the array never holds more than it has room for. As step 2 said, these are facts about the two numbers, which is all the model has.

## 5. The cost of k pushes

The theorem:

```lean
theorem pushSeqCost_initOne_le (k : ℕ) :
    pushSeqCost k DynArrayState.initOne ≤ 3 * k := by
```

Any `k` pushes, starting from `initOne`, cost at most `3k` in total. With the numbers from step 3:

```lean
#guard pushSeqCost 8 DynArrayState.initOne = 15
#guard pushSeqCost 9 DynArrayState.initOne = 24
```

Nine pushes cost 24, under the bound of 27. Notice what the theorem is *not*: it isn't a bound on a single push. The 9th push alone costs 9. "O(1) amortized" is a statement about totals over a sequence, and this theorem states it that way.

### Why 3: the potential method

Where does 3 come from? The proof uses an idea called a *potential*: a number computed from the state that works like a savings account. Cheap pushes pay a little extra into it, and expensive pushes are paid for out of it.

```lean
def phi (s : DynArrayState) : ℤ :=
  2 * (s.size : ℤ) - (s.capacity : ℤ)
```

Φ = 2 × size − capacity. `ℤ` is the integers, which include negative numbers, and `(s.size : ℤ)` converts a natural number to an integer. The conversion is needed because Φ can be negative: for `initOne` it's 2 × 0 − 1 = −1. On `ℕ`, subtraction stops at 0, and 0 − 1 would quietly be 0.

The *amortized cost* of a push is its actual cost plus the change in Φ:

```lean
def pushAmortizedCost (s : DynArrayState) : ℤ :=
  (pushActualCost s : ℤ) + phi (pushState s) - phi s
```

And the key fact is that it's always exactly 3:

```lean
theorem pushAmortizedCost_eq_three (s : DynArrayState)
    (hle : s.size ≤ s.capacity) :
    pushAmortizedCost s = 3 := by
```

Check it by hand. A cheap push costs 1 and raises Φ by 2 (one more element, same capacity): 1 + 2 = 3. An expensive push at size n costs n + 1, and Φ goes from 2n − n = n to 2(n + 1) − 2n = 2: a change of 2 − n. Total: (n + 1) + (2 − n) = 3. The savings from cheap pushes pay for the copying exactly.

Add up the amortized costs of `k` pushes and the changes in Φ cancel in pairs, leaving: total actual cost = 3k − Φ(final) + Φ(start). After at least one push Φ is never negative, and Φ(start) = −1, so the total is at most 3k.

`pushAmortizedCost_eq_three` has the condition `hle : s.size ≤ s.capacity`. It's a fact about the state, and `pushSeq_size_le_capacity_initOne` from step 4 shows it always holds, so the final theorem doesn't need it.

<details>
<summary>Show and explain the proof (optional)</summary>

First the amortized cost of one push:

```lean
theorem pushAmortizedCost_eq_three (s : DynArrayState)
    (hle : s.size ≤ s.capacity) :
    pushAmortizedCost s = 3 := by
  dsimp [pushAmortizedCost, pushActualCost, pushState, phi]
  split_ifs with h
  · push_cast
    ring
  · have heq : s.size = s.capacity := by omega
    push_cast
    omega
```

- `dsimp [...]` unfolds the listed definitions. The goal becomes the formula for the amortized cost written out in full, with an `if` in it.
- `split_ifs with h` splits on `s.size < s.capacity`.
- `push_cast` tidies the conversions from `ℕ` to `ℤ`, for example turning `((s.size + 1 : ℕ) : ℤ)` into `(s.size : ℤ) + 1`, so that the other tactics can see through them.
- The cheap case is pure algebra, so `ring` closes it. The expensive case also needs `size = capacity`, which `omega` gets from `hle` and the failed test, and `omega` then finishes.

Then the sum over many pushes:

```lean
theorem pushSeqCost_telescope (k : ℕ) (s : DynArrayState)
    (hle : ∀ j < k, (pushSeq j s).size ≤ (pushSeq j s).capacity) :
    (pushSeqCost k s : ℤ) = 3 * (k : ℤ) - phi (pushSeq k s) + phi s := by
  induction k with
  | zero =>
    dsimp [pushSeqCost, pushSeq]
    ring
  | succ k ih =>
    dsimp [pushSeqCost, pushSeq]
    have ih_le : ∀ j < k, (pushSeq j s).size ≤ (pushSeq j s).capacity := by
      intro j hj
      exact hle j (by omega)
    have ih_eq := ih ih_le
    have h_last := hle k (by omega)
    have h_amort := pushAmortizedCost_eq_three (pushSeq k s) h_last
    dsimp [pushAmortizedCost] at h_amort
    linarith
```

- `induction k with | zero => … | succ k ih => …` is induction on a number: the case 0, then the case `k + 1` assuming the claim for `k`.
- `hle` needs every state along the way to satisfy `size ≤ capacity`. `∀ j < k, …` means "for every `j` less than `k`".
- For `k + 1`, the proof takes the formula for `k` pushes (`ih_eq`), adds the last push, whose amortized cost is 3 (`h_amort`), and `linarith` combines the two equations. `linarith` proves goals that follow from the hypotheses by adding them up and multiplying by constants, over `ℤ` as well as `ℕ`.

The headline theorem combines this with Φ(start) = −1 and Φ(final) ≥ 0:

```lean
theorem pushSeqCost_initOne_le (k : ℕ) :
    pushSeqCost k DynArrayState.initOne ≤ 3 * k := by
  cases k with
  | zero =>
    dsimp [pushSeqCost]
    omega
  | succ k =>
    have hk : 0 < k + 1 := Nat.succ_pos k
    have _h_tel := pushSeqCost_telescope_initOne (k + 1)
    have _h_phi := phi_pushSeq_initOne_nonneg (k + 1) hk
    omega
```

`cases k` splits on whether `k` is 0 or `k + 1`, with no induction hypothesis. Zero pushes cost 0. For at least one push, the two facts go into context and `omega` finishes, even though they mention integers: `omega` handles `ℤ` and the conversions between `ℕ` and `ℤ`. The underscores in `_h_tel` and `_h_phi` keep Lean's linter quiet, because the proof never refers to those names directly. `omega` just uses everything in context.

</details>

## Spot the fake

### "pushes cost O(1) amortized"

All options compile; the companion file has them.

**Option A**

```lean
def badPhi (s : DynArrayState) : ℤ := -((s.size : ℤ) * s.size)
```

```lean
def badAmortizedCost (s : DynArrayState) : ℤ :=
  (pushActualCost s : ℤ) + badPhi (pushState s) - badPhi s
```

```lean
theorem badAmortizedCost_le_three (s : DynArrayState) :
    badAmortizedCost s ≤ 3 := by
```

**Option B**

```lean
theorem pushSeqCost_initOne_le (k : ℕ) :
    pushSeqCost k DynArrayState.initOne ≤ 3 * k := by
```

**Option C**

```lean
theorem pushActualCost_le_size_add_one (s : DynArrayState) :
    pushActualCost s ≤ s.size + 1 := by
```

<details>
<summary>Show answer</summary>

B.

A proves "amortized cost ≤ 3", but with a different potential, Φ = −size². Amortized cost is a definition, and with a potential that drops fast enough you can make it as small as you like: here each push lowers Φ by 2 × size + 1, which more than cancels the copying. The trouble is that the potential method only bounds the real total if Φ starts low and never goes below where it started. This Φ goes ever more negative, so the bound says nothing about actual cost. An amortized bound is only as good as its potential, which is why the real proof ends in a theorem about `pushSeqCost`, the actual total.

C is true and about the real cost, but it's a worst case for one push. Summing it over `k` pushes gives a bound of roughly k²/2, not 3k.

</details>

## Exercises

**1. Predict.** Starting from `initOne`, what does the 17th push cost? What do the first 16 pushes cost in total?

<details>
<summary>Show answer</summary>

17 and 31. The 17th push finds the array full at size 16 (capacity 16), so it copies 16 elements and writes one. For the total: the expensive pushes among the first 16 are at sizes 1, 2, 4 and 8, costing 2 + 3 + 5 + 9 = 19. The other 12 pushes cost 1 each, so the total is 31, under the bound of 48.

</details>

**2. State it yourself.** Write a statement saying that after `k` pushes from `initOne`, the array holds exactly `k` elements.

<details>
<summary>Show answer</summary>

```lean
theorem pushSeq_initOne_size (k : ℕ) :
    (pushSeq k DynArrayState.initOne).size = k := by
```

The companion file proves it from `pushSeq_size`, since `initOne` starts with size 0.

</details>

**3. Prove it with AI.** The capacity always stays a power of two.

```lean
-- exercise
theorem pushSeq_initOne_capacity (k : ℕ) :
    ∃ j, (pushSeq k DynArrayState.initOne).capacity = 2 ^ j := by
  sorry
```

`∃ j, …` means "there is some `j` such that …". Paste the statement at the end of the companion file, ask an assistant for a proof, and build.

## Lean introduced in this chapter

| You'll see | It means |
| :--- | :--- |
| `structure S where …` | a record type with named fields |
| `s.size` | the field `size` of `s` |
| `⟨a, b⟩` | build a structure from its fields, in order |
| `deriving Repr, DecidableEq` | generate printing and `=` checks, for `#eval` and `#guard` |
| `\| 0, s => … \| k + 1, s => …` | pattern matching on a number of steps |
| `_` | an argument that isn't used |
| `ℤ` | the integers, including negative numbers |
| `(n : ℤ)` | the natural number `n`, converted to an integer |
| `∀ j < k, P j` | `P j` holds for every `j` less than `k` |
| `∃ j, P j` | there is some `j` with `P j` |

## Proof tactics in this chapter (optional)

New ones from the "Show and explain the proof" sections.

| You'll see | It means |
| :--- | :--- |
| `dsimp [f, g]` | unfold the definitions `f` and `g` |
| `push_cast` | tidy conversions such as `((a + 1 : ℕ) : ℤ)` into `(a : ℤ) + 1` |
| `induction k with \| zero => … \| succ k ih => …` | induction on a number |
| `cases k with \| zero => … \| succ k => …` | split on whether `k` is 0, without an induction hypothesis |
| `linarith` | prove a goal by adding up hypotheses and multiplying by constants |
| `omega` on `ℤ` | `omega` also handles integers and conversions from `ℕ` |
