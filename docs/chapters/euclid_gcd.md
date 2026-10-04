# Euclid's GCD

*Needs Binary GCD. Unlocks Extended Euclid.*

This chapter solves the same problem as the last one with a different algorithm. The specification doesn't change at all, and that turns out to be useful: once two algorithms are each proved equal to `Nat.gcd`, they are automatically equal to each other.

The companion file is `Tutorial/EuclideanGCD.lean`.

## 1. The problem

The same as in [Binary GCD](binary_gcd.md): given natural numbers `a` and `b`, find their greatest common divisor, with gcd(a, 0) = a and gcd(0, 0) = 0.

## 2. What "correct" means in Lean

Also the same: the algorithm must return `Nat.gcd a b`. If you've done the Binary GCD chapter, there's nothing new here.

## 3. The algorithm

Euclid's algorithm is over two thousand years old and rests on one fact: when `a` is positive, gcd(a, b) = gcd(b mod a, a). The reason is that b mod a = b − q × a for some whole number `q`, so any number that divides both `a` and `b` also divides `b mod a`, and the other way round. The pairs (a, b) and (b mod a, a) have exactly the same common divisors.

In Python:

```python
def euclid_gcd(a, b):
    if a == 0: return b
    return euclid_gcd(b % a, a)
```

This is how it looks in Lean, from `Amort/GCD/EuclideanGCD.lean`:

```lean
def euclidGcd (a b : ℕ) : ℕ :=
  if a = 0 then b
  else euclidGcd (b % a) a
termination_by a
decreasing_by
  exact Nat.mod_lt b (by omega)
```

If `a` starts out larger than `b`, the first call just swaps them, because `b % a = b` when `b < a`. Here is the trace for (48, 18):

| Call | `b % a` | Next call |
| :--- | :--- | :--- |
| `euclidGcd 48 18` | 18 % 48 = 18 | `euclidGcd 18 48` (the swap) |
| `euclidGcd 18 48` | 48 % 18 = 12 | `euclidGcd 12 18` |
| `euclidGcd 12 18` | 18 % 12 = 6 | `euclidGcd 6 12` |
| `euclidGcd 6 12` | 12 % 6 = 0 | `euclidGcd 0 6` |
| `euclidGcd 0 6` | | returns 6 |

### Why it stops

As in Binary GCD, the last three lines are a proof that the function stops. This time the termination measure is just `a`, the first argument. The recursive call replaces `a` with `b % a`, and a remainder is always smaller than the number you divided by: `b % a < a` whenever `a > 0`. Mathlib calls that fact `Nat.mod_lt`, and the proof after `decreasing_by` uses it by name. `exact` means "this is the proof". The `(by omega)` supplies the condition `0 < a`, which `omega` works out from the fact that we're in the `else` branch, where `a ≠ 0`.

### Running it

```lean
#guard Nat.euclidGcd 48 18 = 6
#guard Nat.euclidGcd 105 252 = 21
#guard Nat.euclidGcd 0 7 = 7
#guard Nat.euclidGcd 0 0 = 0
```

## 4. The correctness theorem

```lean
theorem euclidGcd_eq_gcd (a b : ℕ) : euclidGcd a b = Nat.gcd a b
```

It has the same shape as `binaryGcd_eq_gcd`: no conditions, and the right-hand side is the specification. Because both algorithms are proved equal to `Nat.gcd`, proving they agree with each other takes one line:

```lean
theorem euclid_eq_binary (a b : ℕ) : Nat.euclidGcd a b = Nat.binaryGcd a b := by
  rw [Nat.euclidGcd_eq_gcd, Nat.binaryGcd_eq_gcd]
```

`rw` means "rewrite": it replaces the left side of an equation with its right side. The proof rewrites `Nat.euclidGcd a b` to `Nat.gcd a b`, then does the same to `Nat.binaryGcd a b`, and both sides are now identical. Comparing the two algorithms directly, step by step, would be a long and fiddly proof. Going through a shared specification avoids it.

## 5. How many steps

We count recursive calls. Each call does one `%`.

```lean
def euclidGcdWithSteps (a b : ℕ) : ℕ × ℕ :=
  if a = 0 then (b, 0)
  else
    let (g, s) := euclidGcdWithSteps (b % a) a
    (g, 1 + s)
```

`let (g, s) := …` takes the pair returned by the recursive call apart: `g` is the gcd and `s` is the count so far. As in the last chapter, one theorem ties the counting version to the real algorithm, and another bounds the count:

```lean
theorem euclidGcdWithSteps_fst (a b : ℕ) : (euclidGcdWithSteps a b).1 = euclidGcd a b
```

```lean
theorem euclidGcdWithSteps_snd_le_two_mul_size_min (a b : ℕ) :
    (euclidGcdWithSteps a b).2 ≤ 2 * Nat.size (min a b) + 1
```

The bound depends only on the *smaller* input. If one number has a million digits and the other is 6, which has 3 bits, Euclid's algorithm finishes in at most 2 × 3 + 1 = 7 calls. After the first call or two, the big number is gone.

The reason is this lemma, also in the reference file:

```lean
lemma mod_two_mul_lt {a b : ℕ} (hb : 0 < b) (hba : b ≤ a) : 2 * (a % b) < a
```

Two new things to read here:

- **Curly braces.** `{a b : ℕ}` makes `a` and `b` *implicit*. When you use the lemma, you don't pass them; Lean works them out from the other arguments.
- **Hypotheses.** `(hb : 0 < b)` and `(hba : b ≤ a)` are conditions: to use the lemma you have to supply proofs that `0 < b` and `b ≤ a`. Conditions like these, which describe the inputs, are normal. What you have to watch for is a condition that quietly assumes the thing the theorem is supposed to prove.

The lemma says that when `b ≤ a`, the remainder `a % b` is less than half of `a`. Every two calls, the numbers shrink by at least half, which means they lose at least one bit. That's where "2 × bits + 1" comes from.

### Fewer calls isn't the same as faster

```lean
#guard Nat.euclidGcdWithSteps 48 18 = (6, 4)
#guard Nat.binaryGcdWithSteps 48 18 = (6, 6)
```

On (48, 18), Euclid makes 4 calls and binary GCD makes 6. That doesn't make Euclid faster, because its calls cost more. A `%` on large numbers is a full division, while binary GCD's calls only halve and subtract. Which one wins depends on the numbers and the hardware. The theorems count calls and say so; they don't claim anything about running time. When you read a complexity theorem, the first question is always "what exactly is being counted?"

## Spot the fake

### "euclidGcd is correct"

**Option A**

```lean
def fakeEuclidAlgo (a b : ℕ) : ℕ := Nat.gcd a b

theorem fakeEuclidAlgo_eq (a b : ℕ) : fakeEuclidAlgo a b = Nat.gcd a b := rfl
```

**Option B**

```lean
theorem euclidGcd_dvd_left (a b : ℕ) : Nat.euclidGcd a b ∣ a
```

**Option C**

```lean
theorem euclidGcd_eq_gcd (a b : ℕ) : euclidGcd a b = Nat.gcd a b
```

<details>
<summary>Show answer</summary>

C.

A's "algorithm" is the specification under another name, so the theorem is true by definition (`rfl` means "both sides are the same by definition") and says nothing about Euclid's algorithm. This isn't a made-up example. While this repository was being built, an AI agent defined a function named `bfs` as the shortest-path specification, then proved "`bfs` is correct" in exactly this way. The real BFS code sat next to it, unproved. The giveaway is to look at the definition: is it an algorithm, or is it the answer?

B is a third of the specification: it only says the result divides `a`. A function that always returns 1 passes it.

</details>

## Exercises

**1. Predict.** What does `#eval Nat.euclidGcdWithSteps 105 252` print? What about `#eval Nat.euclidGcdWithSteps 252 105`?

<details>
<summary>Show answer</summary>

`(21, 3)` and `(21, 4)`. With (105, 252) the calls go (105, 252) → (42, 105) → (21, 42) → (0, 21), which is three calls. With (252, 105), the first call only swaps the arguments, so it makes one extra call.

</details>

**2. State it yourself.** Write a statement saying: if `a` divides `b`, then Euclid's algorithm returns `a`.

<details>
<summary>Show answer</summary>

```lean
theorem euclidGcd_eq_left_of_dvd (a b : ℕ) (h : a ∣ b) : Nat.euclidGcd a b = a := by
```

Did you add a condition that `a` is positive? Many people do, and the companion file has that version too:

```lean
theorem euclidGcd_eq_left_of_pos_of_dvd (a b : ℕ) (_ha : 0 < a) (h : a ∣ b) :
    Nat.euclidGcd a b = a := by
```

Both are true, but the second is weaker: it says nothing when `a = 0`. The condition isn't needed, because if 0 divides `b` then `b` is 0, and gcd(0, 0) = 0. There's a clue in the name `_ha`. A leading underscore is Lean's convention for a hypothesis the proof never uses; without it, Lean's linter would warn that `ha` is unused. When a condition goes unused, you can usually drop it and get a stronger theorem.

</details>

**3. Prove it with AI.**

```lean
-- exercise
theorem euclidGcd_zero_left (b : ℕ) : Nat.euclidGcd 0 b = b := by
  sorry
```

Paste it at the end of the companion file, ask an assistant for a proof, and build. Then compare its statement with yours, symbol by symbol, before accepting it.

## Lean introduced in this chapter

| You'll see | It means |
| :--- | :--- |
| `{a b : ℕ}` | implicit arguments: Lean fills them in |
| `(hb : 0 < b)` | a hypothesis: you must supply a proof of `0 < b` |
| `_ha` | a hypothesis the proof never uses |
| `min a b` | the smaller of `a` and `b` |
| `let (g, s) := e` | take the pair `e` apart into `g` and `s` |
| `exact p` | "`p` is the proof" |
| `rw [h]` | rewrite using the equation `h` |
| `rfl` | "both sides are the same by definition" |
| `Nat.euclidGcd` vs `euclidGcd` | the same function; the long name is used outside `namespace Nat` |
