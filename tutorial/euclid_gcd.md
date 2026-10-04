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

<details>
<summary>Show and explain the proof (optional)</summary>

Here is the proof of `euclidGcd_eq_gcd`, from `Amort/GCD/EuclideanGCD.lean`:

```lean
theorem euclidGcd_eq_gcd (a b : ℕ) : euclidGcd a b = Nat.gcd a b := by
  induction a using Nat.strong_induction_on generalizing b with
  | h a ih =>
    rw [euclidGcd.eq_def]
    split_ifs with ha
    · rw [ha, Nat.gcd_zero_left]
    · have hlt : b % a < a := Nat.mod_lt b (by omega)
      rw [ih (b % a) hlt a]
      conv_rhs => rw [Nat.gcd.eq_def, if_neg ha]
```

**The idea.** It's much shorter than the binary GCD proof, and here's why: Lean defines `Nat.gcd` itself with Euclid's recursion. Once the recursive call is known to be right, both sides unfold to the same thing.

**Line by line.**

- `induction a using Nat.strong_induction_on` is *strong induction*: to prove the claim for `a`, you may assume it for every number smaller than `a`, not just for `a − 1`. We need that because the recursive call is on `b % a`, which can be any number below `a`. `ih` says: for every `m < a` and every `b`, `euclidGcd m b = Nat.gcd m b`.
- `generalizing b` is what puts "every `b`" into `ih`. The recursive call passes `a` as its second argument, not `b`, so a hypothesis about one fixed `b` wouldn't help.
- `split_ifs with ha` splits the goal into the two branches of `if a = 0`. In the first branch `ha : a = 0`; in the second `ha : ¬a = 0`. The `·` bullets mark the proof of each branch.
- First branch: the goal is `b = Nat.gcd a b`. `rw [ha]` replaces `a` with 0, and Mathlib's `Nat.gcd_zero_left` says `Nat.gcd 0 b = b`.
- Second branch: the goal is `euclidGcd (b % a) a = Nat.gcd a b`. `hlt` proves the recursive call is on a smaller number, so `ih (b % a) hlt a` rewrites the left side to `Nat.gcd (b % a) a`. Then `conv_rhs => rw [Nat.gcd.eq_def, if_neg ha]` unfolds `Nat.gcd a b` on the right, and it unfolds to exactly `Nat.gcd (b % a) a`.

</details>

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

<details>
<summary>Show and explain the proof (optional)</summary>

The halving lemma first:

```lean
lemma mod_two_mul_lt {a b : ℕ} (hb : 0 < b) (hba : b ≤ a) : 2 * (a % b) < a := by
  have hdiv := Nat.div_add_mod a b
  have hmod := Nat.mod_lt a hb
  have hq0 : 0 < a / b := Nat.div_pos hba hb
  have hq_cases : a / b = 1 ∨ 2 ≤ a / b := by omega
  rcases hq_cases with hq1 | hq2
  · have h1 : b * (a / b) = b := by rw [hq1, Nat.mul_one]
    omega
  · have h2 : 2 * b ≤ b * (a / b) := by
      rw [Nat.mul_comm 2 b]
      exact Nat.mul_le_mul_left b hq2
    omega
```

**The idea.** Write `a = b × q + r`, where `q` is the quotient and `r < b` is the remainder. If `q = 1`, then `a = b + r`, and `r < b` gives `2r < a`. If `q ≥ 2`, then `a ≥ 2b > 2r`.

**Line by line.**

- The three `have`s collect facts from Mathlib: `hdiv : b * (a / b) + a % b = a`, `hmod : a % b < b`, and `hq0 : 0 < a / b`.
- `hq_cases` says the quotient is 1 or at least 2. `∨` means "or". `omega` proves it from `hq0`.
- `rcases hq_cases with hq1 | hq2` splits the proof in two: one where `hq1 : a / b = 1`, one where `hq2 : 2 ≤ a / b`.
- Why the extra `h1` and `h2`? `omega` only handles addition and multiplication by fixed numbers. It can't reason about `b * (a / b)`, a product of two unknowns, so it treats the product as one more unknown number. `h1` and `h2` tell it what it needs to know about that product, and then `omega` finishes both cases.

From this lemma, `size_mod_add_one_le` in the same file gets "the remainder has at least one bit fewer". The bound itself is proved two calls at a time:

```lean
lemma euclideanGcdSteps_le_two_mul_size_of_le (a : ℕ) :
    ∀ b, a ≤ b → euclideanGcdSteps a b ≤ 2 * Nat.size a := by
  induction a using Nat.strong_induction_on with
  | h a ih =>
    intro b hab
    by_cases ha : a = 0
    · rw [euclideanGcdSteps.eq_def, dif_pos ha]
      omega
    · rw [euclideanGcdSteps.eq_def, dif_neg ha]
      have ha_pos : 0 < a := Nat.pos_of_ne_zero ha
      have hr1_lt : b % a < a := Nat.mod_lt b ha_pos
      by_cases hr1 : b % a = 0
      · rw [euclideanGcdSteps.eq_def, dif_pos hr1]
        have : 0 < Nat.size a := Nat.size_pos.mpr ha_pos
        omega
      · have hr1_pos : 0 < b % a := Nat.pos_of_ne_zero hr1
        rw [euclideanGcdSteps.eq_def, dif_neg hr1]
        have hr2_lt : a % (b % a) < b % a := Nat.mod_lt a hr1_pos
        have hr2_le : a % (b % a) ≤ b % a := Nat.le_of_lt hr2_lt
        have hih := ih (a % (b % a)) (by omega) (b % a) hr2_le
        have hstep : Nat.size (a % (b % a)) + 1 ≤ Nat.size a :=
          size_mod_add_one_le hr1_pos (Nat.le_of_lt hr1_lt)
        omega
```

It counts with `euclideanGcdSteps`, the count-only version, which `euclidGcdWithSteps_snd` proves equal to the count in `euclidGcdWithSteps`. When `a ≤ b`, two calls take the pair (a, b) to (b % a, a) and then to (a % (b % a), b % a). The proof follows those two calls:

- `intro b hab` takes the `∀ b, a ≤ b →` apart: from here on `b` is a fixed number and `hab : a ≤ b`.
- `by_cases ha : a = 0` splits on whether `a` is 0, like `split_ifs` but for any condition. If it is, there are no calls and the bound holds.
- Otherwise the proof unfolds one call and splits again on whether `b % a = 0`. If it is, that was the only call, and `2 * Nat.size a` is at least 2 because `a > 0`.
- Otherwise it unfolds the second call. `hih` is the induction hypothesis applied to the pair after two calls, and `hstep` says its first number has at least one bit fewer than `a`. So two calls cost 2 and lose at least one bit, and `omega` adds it up: 2 + 2 × (bits − 1) ≤ 2 × bits.

The headline theorem `euclideanGcdSteps_le_two_mul_size_min` then deals with the case `b < a`: the first call only swaps the arguments, which is where the `+ 1` comes from.

</details>

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

## Proof tactics in this chapter (optional)

New ones from the "Show and explain the proof" sections. The [Binary GCD](binary_gcd.md) chapter has the earlier ones.

| You'll see | It means |
| :--- | :--- |
| `induction a using Nat.strong_induction_on` | strong induction: assume the claim for every number smaller than `a` |
| `generalizing b` | let the induction hypothesis hold for every `b`, not just this one |
| `split_ifs with h` | split the goal into the branches of an `if`, naming the condition `h` |
| `·` | starts the proof of one goal after a split |
| `conv_rhs => rw [h]` | rewrite only the right-hand side of the goal |
| `if_neg h` | pick the `else` branch of a plain `if c`, given `h : ¬c` |
| `P ∨ Q` | `P` or `Q` |
| `rcases h with h₁ \| h₂` | split `h : P ∨ Q` into one case with `h₁ : P` and one with `h₂ : Q` |
| `intro x h` | take `∀ x, P → …` apart: fix `x` and assume `h : P` |
| `by_cases h : c` | split into the case where `c` holds and the case where it doesn't |
