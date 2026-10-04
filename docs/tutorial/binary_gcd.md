# Binary GCD

*The first node in the tree. It unlocks Euclid's GCD, Insertion Sort, Binary Search, Dynamic Array and Modular Exponentiation.*

New to these chapters? Read [Start here](intro.md) first. It explains how the chapters work, what to read beforehand and how to run the examples.

The companion file for this chapter is `Tutorial/BinaryGCD.lean`. You can read everything here without it.

## 1. The problem

The greatest common divisor of two natural numbers `a` and `b` is the largest number that divides both of them. For gcd(48, 18), the divisors of 48 are 1, 2, 3, 4, 6, 8, 12, 16, 24 and 48, the divisors of 18 are 1, 2, 3, 6, 9 and 18, and the largest number on both lists is 6.

Zero needs a decision:

- gcd(a, 0) = a. Every number divides 0, so the common divisors of `a` and 0 are just the divisors of `a`.
- gcd(0, 0) = 0. Every number divides 0, so there is no largest common divisor, and "largest" has to be read differently. The next step explains how.

## 2. What "correct" means in Lean

We don't have to define gcd ourselves. Mathlib, the standard maths library for Lean, has `Nat.gcd`, and three facts about it pin it down:

```lean
example : ∀ a b : ℕ, Nat.gcd a b ∣ a := Nat.gcd_dvd_left
example : ∀ a b : ℕ, Nat.gcd a b ∣ b := Nat.gcd_dvd_right
example : ∀ {a b d : ℕ}, d ∣ a → d ∣ b → d ∣ Nat.gcd a b := Nat.dvd_gcd
```

This is the first Lean in the tutorial, so here it is piece by piece:

- `ℕ` is the natural numbers: 0, 1, 2 and so on.
- `∀ a b : ℕ,` means "for all natural numbers `a` and `b`".
- `x ∣ y` means "`x` divides `y`". The symbol is a special vertical bar (typed `\mid` in the editor), not the `|` key.
- `→` means "implies". The third line reads: if `d` divides `a`, and `d` divides `b`, then `d` divides `Nat.gcd a b`.
- `example : claim := proof` asks Lean to check that the claim holds. The part after `:=` is the proof, here just the name of a theorem already in Mathlib. These three lines are in the companion file, so Lean confirms on every build that the claims are exactly what Mathlib proves.

The first two lines say that `Nat.gcd a b` is a common divisor. The third says it is the greatest one, in a specific sense: every other common divisor divides it. That sense settles gcd(0, 0). Every number is a common divisor of 0 and 0, and the only number they all divide is 0.

None of this mentions an algorithm, and that's deliberate: the definition of gcd is orthogonal to any algorithm that computes it. Binary GCD, Euclid's algorithm and a brute-force search are all correct exactly when they return `Nat.gcd a b`.

## 3. The algorithm

Binary GCD is due to Josef Stein (1967). It never divides except by 2: it only checks whether numbers are even, halves them, and subtracts. It rests on three facts:

1. If `a` and `b` are both even, gcd(a, b) = 2 × gcd(a/2, b/2).
2. If `a` is even and `b` is odd, gcd(a, b) = gcd(a/2, b). Since `b` is odd, 2 can't be a common factor, so it's safe to drop it from `a`. The same works with the roles swapped.
3. If both are odd and b ≤ a, then a − b is even, and gcd(a, b) = gcd((a − b)/2, b).

In Python:

```python
def binary_gcd(a, b):
    if a == 0: return b
    if b == 0: return a
    if a % 2 == 0 and b % 2 == 0: return 2 * binary_gcd(a // 2, b // 2)
    if a % 2 == 0: return binary_gcd(a // 2, b)
    if b % 2 == 0: return binary_gcd(a, b // 2)
    if b <= a: return binary_gcd((a - b) // 2, b)
    return binary_gcd(a, (b - a) // 2)
```

This is how it looks in Lean, from `Amort/GCD/BinaryGCD.lean`:

```lean
def binaryGcd (a b : ℕ) : ℕ :=
  if ha : a = 0 then b
  else if hb : b = 0 then a
  else if ha_even : a % 2 = 0 then
    if hb_even : b % 2 = 0 then
      2 * binaryGcd (a / 2) (b / 2)
    else
      binaryGcd (a / 2) b
  else if hb_even : b % 2 = 0 then
    binaryGcd a (b / 2)
  else
    if h_le : b ≤ a then
      binaryGcd ((a - b) / 2) b
    else
      binaryGcd a ((b - a) / 2)
termination_by a + b
decreasing_by
  all_goals omega
```

Here is how to read the Lean:

- `(a b : ℕ) : ℕ` says both inputs and the output are natural numbers.
- `/` and `%` on natural numbers round down, like Python's `//` and `%`.
- `if ha : a = 0 then` is an ordinary `if` that also gives the condition a name, `ha`. The code never uses these names. The termination proof does, because it needs to know which branch it is in.
- The last three lines are our first example of a Lean proof. They are there because Lean won't accept a recursive function until it's convinced the function stops on every input. The next section explains how.

### Why it stops

`termination_by a + b` promises that `a + b` gets smaller with every recursive call. `decreasing_by all_goals omega` proves that promise. `omega` is a built-in tactic that proves facts about addition, subtraction and comparison of numbers on its own, and `all_goals` runs it once for each recursive call.

You can check the promise by hand. A recursive call only happens when `a` and `b` are both at least 1:

- Both even: a/2 + b/2 is less than a + b.
- `a` even, `b` odd: a/2 + b is less than a + b, because a ≥ 2.
- Both odd, b ≤ a: (a − b)/2 + b is at most (a + b)/2, which is less than a + b.

A natural number can't get smaller forever, so the recursion always reaches `a = 0` or `b = 0`.

### Running it

```lean
#guard Nat.binaryGcd 48 18 = 6
#guard Nat.binaryGcd 105 252 = 21
#guard Nat.binaryGcd 0 7 = 7
#guard Nat.binaryGcd 0 0 = 0
```

`#guard` evaluates a true-or-false expression and stops the build if it's false. These chapters use `#guard` rather than a comment like `-- prints 6`, because nothing checks a comment. You can also type `#eval Nat.binaryGcd 48 18` in the companion file and Lean will print the result.

The name is `Nat.binaryGcd` here because the reference file defines it inside `namespace Nat`. Inside that file it's just `binaryGcd`.

## 4. The correctness theorem

```lean
theorem binaryGcd_eq_gcd (a b : ℕ) : binaryGcd a b = Nat.gcd a b
```

This reads: there is a theorem called `binaryGcd_eq_gcd`, and for any natural numbers `a` and `b`, `binaryGcd a b` equals `Nat.gcd a b`. (In the source file it's followed by `:= by` and the proof, which we skip.)

Two things make this the right statement:

- **It has no conditions.** The only inputs are `(a b : ℕ)`, so it covers every pair of numbers, zeros included. A version with an extra input such as `(ha : 0 < a)` would say nothing about `a = 0`.
- **The right-hand side is the specification from step 2.** It isn't something built out of `binaryGcd` itself.

The proof goes through the branches of `binaryGcd` one by one. In each branch it uses the matching fact from step 3 to show the recursive call has the same gcd as the original pair. You don't need it for the rest of the chapter, but if you're curious, open the section below.

<details>
<summary>Show and explain the proof (optional)</summary>

Here is the whole proof, from `Amort/GCD/BinaryGCD.lean`:

```lean
theorem binaryGcd_eq_gcd (a b : ℕ) : binaryGcd a b = Nat.gcd a b := by
  induction a, b using binaryGcd.induct with
  | case1 b =>
    rw [binaryGcd.eq_def, dif_pos rfl, Nat.gcd_zero_left]
  | case2 a ha =>
    rw [binaryGcd.eq_def, dif_neg ha, dif_pos rfl, Nat.gcd_zero_right]
  | case3 a b ha hb ha_even hb_even ih =>
    rw [binaryGcd.eq_def, dif_neg ha, dif_neg hb, dif_pos ha_even, dif_pos hb_even, ih]
    exact (gcd_even_even ha_even hb_even).symm
  | case4 a b ha hb ha_even hb_odd ih =>
    rw [binaryGcd.eq_def, dif_neg ha, dif_neg hb, dif_pos ha_even, dif_neg hb_odd, ih]
    exact (gcd_even_odd ha_even (by omega)).symm
  | case5 a b ha hb ha_odd hb_even ih =>
    rw [binaryGcd.eq_def, dif_neg ha, dif_neg hb, dif_neg ha_odd, dif_pos hb_even, ih]
    exact (gcd_odd_even (by omega) hb_even).symm
  | case6 a b ha hb ha_odd hb_odd hba ih =>
    rw [binaryGcd.eq_def, dif_neg ha, dif_neg hb, dif_neg ha_odd, dif_neg hb_odd, dif_pos hba, ih]
    exact (gcd_odd_odd_sub_div_two_left (by omega) (by omega) hba).symm
  | case7 a b ha hb ha_odd hb_odd hnba ih =>
    rw [binaryGcd.eq_def, dif_neg ha, dif_neg hb, dif_neg ha_odd, dif_neg hb_odd, dif_neg hnba, ih]
    exact (gcd_odd_odd_sub_div_two_right (by omega) (by omega) (by omega)).symm
```

**The idea.** Assume the recursive call returns the right answer, and show that the current call then does too. That's induction, and it's the same reasoning you'd use to convince yourself a recursive function is right.

**Line by line.**

- `:= by` starts a proof written as a sequence of *tactics*: commands that each transform what's left to prove (the *goal*) until nothing is left.
- `induction a, b using binaryGcd.induct with` splits the proof into one case per branch of `binaryGcd`. Lean built `binaryGcd.induct` from the definition, so there are seven cases: two base cases (`a = 0`, `b = 0`) and five recursive ones. In each recursive case you also get `ih`, the *induction hypothesis*: the theorem already holds for the arguments of the recursive call. This is allowed because the termination proof showed that those arguments are smaller.
- `| case3 a b ha hb ha_even hb_even ih =>` names what this case knows: `ha : ¬a = 0`, `hb : ¬b = 0`, `ha_even : a % 2 = 0`, `hb_even : b % 2 = 0`, and `ih`.
- `rw [binaryGcd.eq_def, …]` rewrites the goal step by step. `binaryGcd.eq_def` unfolds `binaryGcd a b` into its `if` chain. `dif_pos h` picks the `then` branch of an `if`, using `h` as proof that the condition holds, and `dif_neg h` picks the `else` branch. (`rfl` proves `0 = 0` in the base cases.) After those, the goal in case 3 is `2 * binaryGcd (a / 2) (b / 2) = Nat.gcd a b`, and rewriting with `ih` turns it into `2 * Nat.gcd (a / 2) (b / 2) = Nat.gcd a b`.
- `exact (gcd_even_even ha_even hb_even).symm` closes the goal with the matching fact from step 3. `gcd_even_even` states the equation the other way round, and `.symm` flips it.
- `(by omega)` appears where a lemma wants `b % 2 = 1` but the case only knows `¬b % 2 = 0`. `omega` fills that gap.
- In the base cases, `rw` finishes by itself: once both sides are identical, it closes the goal.

The step-3 facts are short lemmas in the same file. Here is the one for "`a` even, `b` odd":

```lean
lemma gcd_even_odd {a b : ℕ} (ha : a % 2 = 0) (hb : b % 2 = 1) :
    Nat.gcd a b = Nat.gcd (a / 2) b := by
  have h2 : a = 2 * (a / 2) := by omega
  conv_lhs => rw [h2]
  exact (coprime_two_of_odd hb).gcd_mul_left_cancel (a / 2)
```

- `have h2 : … := by omega` proves an intermediate fact and names it `h2`.
- `conv_lhs => rw [h2]` rewrites `a` to `2 * (a / 2)` on the left-hand side only. A plain `rw` would also rewrite the `a` inside `a / 2` on the right.
- The goal is now `Nat.gcd (2 * (a / 2)) b = Nat.gcd (a / 2) b`. Mathlib's `Nat.Coprime.gcd_mul_left_cancel` says that a factor sharing nothing with `b` can be dropped from a gcd. `coprime_two_of_odd hb` proves that 2 shares nothing with an odd `b`, and the dot calls the Mathlib theorem on that proof.

</details>

## 5. How many steps

We count recursive calls. Each call does up to two evenness checks and then one of three things: halve one number, halve both, or subtract and halve.

To count the calls, the repository has a second version of the function that returns a pair: the answer, and the number of calls made. Here are its first lines, from `Amort/GCD/StepCount.lean`:

```lean
def binaryGcdWithSteps (a b : ℕ) : ℕ × ℕ :=
  if _ha : a = 0 then (b, 0)
  else if _hb : b = 0 then (a, 0)
  else if ha_even : a % 2 = 0 then
    if hb_even : b % 2 = 0 then
      let r := binaryGcdWithSteps (a / 2) (b / 2)
      (2 * r.1, r.2 + 1)
```

`ℕ × ℕ` is a pair of natural numbers. `let r := …` names the result of the recursive call, and `r.1` and `r.2` are the two parts of the pair. Every branch returns the answer from the recursive call and adds 1 to its count.

A counter only means something if it counts the real algorithm. A second function could easily drift from the first, so the repository proves they agree:

```lean
theorem binaryGcdWithSteps_fst (a b : ℕ) :
    (binaryGcdWithSteps a b).1 = binaryGcd a b
```

The first part of the pair is exactly `binaryGcd a b`, on every input. So the counting version runs the same algorithm, and the bound below is about `binaryGcd`:

```lean
theorem binaryGcdWithSteps_snd_le_size_add_size (a b : ℕ) :
    (binaryGcdWithSteps a b).2 ≤ Nat.size a + Nat.size b
```

`Nat.size n` is the number of bits in `n`. For example, `Nat.size 6 = 3` because 6 is `110` in binary, and `Nat.size 0 = 0`. So the theorem says the number of calls is at most the total number of bits in the two inputs. That makes sense: every call removes at least one bit from at least one of the numbers. Two 64-bit inputs need at most 128 calls, even though the numbers themselves can be as large as 2⁶⁴.

<details>
<summary>Show and explain the proof (optional)</summary>

The proof of the bound is two lines:

```lean
theorem binaryGcdWithSteps_snd_le_size_add_size (a b : ℕ) :
    (binaryGcdWithSteps a b).2 ≤ Nat.size a + Nat.size b := by
  rw [binaryGcdWithSteps_snd]
  exact binaryGcdSteps_le_size_add_size a b
```

The file has a third function, `binaryGcdSteps`, which returns only the count. `binaryGcdWithSteps_snd` proves that it equals the count in `binaryGcdWithSteps`, so `rw` swaps one for the other, and `exact` hands over the real work to this theorem:

```lean
theorem binaryGcdSteps_le_size_add_size (a b : ℕ) :
    binaryGcdSteps a b ≤ Nat.size a + Nat.size b := by
  induction a, b using binaryGcdSteps.induct with
  | case1 b =>
    rw [binaryGcdSteps.eq_def, dif_pos rfl]
    omega
  | case2 a ha =>
    rw [binaryGcdSteps.eq_def, dif_neg ha, dif_pos rfl]
    omega
  | case3 a b ha hb ha_even hb_even ih =>
    rw [binaryGcdSteps.eq_def, dif_neg ha, dif_neg hb, dif_pos ha_even, dif_pos hb_even]
    have := size_div_two a (by omega)
    have := size_div_two b (by omega)
    omega
  | case4 a b ha hb ha_even hb_odd ih =>
    rw [binaryGcdSteps.eq_def, dif_neg ha, dif_neg hb, dif_pos ha_even, dif_neg hb_odd]
    have := size_div_two a (by omega)
    omega
  | case5 a b ha hb ha_odd hb_even ih =>
    rw [binaryGcdSteps.eq_def, dif_neg ha, dif_neg hb, dif_neg ha_odd, dif_pos hb_even]
    have := size_div_two b (by omega)
    omega
  | case6 a b ha hb ha_odd hb_odd hba ih =>
    rw [binaryGcdSteps.eq_def, dif_neg ha, dif_neg hb, dif_neg ha_odd, dif_neg hb_odd,
      dif_pos hba]
    have := size_sub_div_two_le a b (by omega)
    omega
  | case7 a b ha hb ha_odd hb_odd hnba ih =>
    rw [binaryGcdSteps.eq_def, dif_neg ha, dif_neg hb, dif_neg ha_odd, dif_neg hb_odd,
      dif_neg hnba]
    have := size_sub_div_two_le b a (by omega)
    omega
```

**The idea.** Every call removes at least one bit from at least one of the numbers, so there can't be more calls than there are bits.

**Line by line.** The shape is the same as the correctness proof: one case per branch, unfold the definition, pick the branch. Take case 4, where `a` is even and `b` is odd. After the `rw`, the goal is `1 + binaryGcdSteps (a / 2) b ≤ Nat.size a + Nat.size b`, and `ih` says `binaryGcdSteps (a / 2) b ≤ Nat.size (a / 2) + Nat.size b`. The missing piece is that halving removes one bit, which is this lemma from the same file:

```lean
lemma size_div_two (a : ℕ) (ha : 0 < a) : Nat.size (a / 2) + 1 = Nat.size a
```

`have := size_div_two a (by omega)` adds that fact for our `a` (an unnamed `have` is called `this`). Then `omega` finishes. `omega` knows nothing about `Nat.size`, but it doesn't need to: it treats `Nat.size a`, `Nat.size (a / 2)` and `binaryGcdSteps (a / 2) b` as unknown numbers, and the inequality follows from the facts in context by plain addition. Cases 6 and 7 use a similar lemma for subtract-and-halve:

```lean
lemma size_sub_div_two_le (a b : ℕ) (ha : 0 < a) :
    Nat.size ((a - b) / 2) + 1 ≤ Nat.size a
```

</details>

What this doesn't count is the work inside a call. For numbers too big for one machine word, halving and subtracting take time proportional to the number of bits. So for two n-bit inputs, the total work is on the order of n² bit operations. That part isn't formalized in this repository; the theorem is only about calls.

The repository also states this bound with Mathlib's big-O notation (`Amort/GCD/Asymptotics.lean`). We'll learn to read big-O statements at the sorting lower bound node.

```lean
#guard Nat.binaryGcdWithSteps 48 18 = (6, 6)
#guard Nat.binaryGcdWithSteps 105 252 = (21, 5)
```

## Spot the fake

Every option below is a real Lean theorem that compiles; they're all in the companion file. The question is which one actually proves the claim. (`∧` means "and".)

### Round 1: "binaryGcd is correct"

**Option A**

```lean
theorem binaryGcd_dvd_both (a b : ℕ) :
    Nat.binaryGcd a b ∣ a ∧ Nat.binaryGcd a b ∣ b
```

**Option B**

```lean
theorem binaryGcd_48_18 : Nat.binaryGcd 48 18 = 6
```

**Option C**

```lean
theorem binaryGcd_eq_gcd (a b : ℕ) : binaryGcd a b = Nat.gcd a b
```

<details>
<summary>Show answer</summary>

Only C.

A is true, but it's half of the specification from step 2. It says the result divides both inputs, not that it's the greatest number that does. A function that always returns 1 passes it too. The companion file defines such a function, `alwaysOne`, and proves `alwaysOne_dvd_both`.

B is a single test case. Tests are useful, but this one says nothing about any other input.

</details>

### Round 2: "binaryGcd makes at most bits(a) + bits(b) calls"

**Option A**

```lean
def gcdCost (a b : ℕ) : ℕ := Nat.size a + Nat.size b

theorem gcdCost_le (a b : ℕ) :
    gcdCost a b ≤ Nat.size a + Nat.size b :=
  le_refl _
```

**Option B**

```lean
theorem binaryGcdWithSteps_fst (a b : ℕ) :
    (binaryGcdWithSteps a b).1 = binaryGcd a b
```

```lean
theorem binaryGcdWithSteps_snd_le_size_add_size (a b : ℕ) :
    (binaryGcdWithSteps a b).2 ≤ Nat.size a + Nat.size b
```

**Option C**

```lean
theorem binaryGcdSteps_le_val_add (a b : ℕ) :
    Nat.binaryGcdSteps a b ≤ a + b
```

<details>
<summary>Show answer</summary>

B.

A defines the cost as the bound and then proves the cost is at most itself. Nothing connects `gcdCost` to `binaryGcd`. You could put any formula on the right and the proof would still work. When an AI agent first wrote this repository's complexity proofs, about fifty of them had exactly this shape. It looks convincing because the name says "cost".

C is about the real step counter and it's true, but it's a much weaker claim. `a + b` is the size of the numbers, not the number of bits. For two 64-bit inputs it allows about 2⁶⁵ calls instead of 128.

</details>

## Exercises

**1. Predict.** What does `#eval Nat.binaryGcd 60 24` print? And `#eval Nat.binaryGcdWithSteps 60 24`?

<details>
<summary>Show answer</summary>

`12` and `(12, 6)`. The calls go (60, 24) → (30, 12) → (15, 6) → (15, 3) → (6, 3) → (3, 3) → (0, 3). That's six recursive calls, and the last pair returns 3. The first two calls each doubled the result, so the answer is 2 × 2 × 3 = 12. The companion file checks both answers with `#guard`.

</details>

**2. State it yourself.** Write a Lean statement saying that binary GCD gives the same answer if you swap the inputs. Don't worry about the proof; just the statement.

<details>
<summary>Show answer</summary>

```lean
theorem binaryGcd_comm (a b : ℕ) : Nat.binaryGcd a b = Nat.binaryGcd b a := by
  rw [Nat.binaryGcd_eq_gcd, Nat.binaryGcd_eq_gcd, Nat.gcd_comm]
```

The statement is everything before `:=`. The proof, in case you're curious, rewrites both sides to `Nat.gcd` using the correctness theorem, then uses Mathlib's fact that `Nat.gcd` doesn't care about order. This is the payoff of having a specification that doesn't mention the algorithm.

</details>

**3. Prove it with AI.** Here is a statement with no proof yet (`sorry` is Lean's placeholder for a missing proof):

```lean
-- exercise
theorem binaryGcd_zero_right (a : ℕ) : Nat.binaryGcd a 0 = a := by
  sorry
```

Paste it at the end of the companion file, ask an AI assistant to replace `sorry` with a proof, and build. If Lean accepts the proof, you're done; you don't need to understand it. Do check that the assistant didn't change the statement. If it came back with, say, an extra `(ha : 0 < a)`, that's a different and weaker theorem, and you should say no.

## Lean introduced in this chapter

| You'll see | It means |
| :--- | :--- |
| `ℕ` | the natural numbers 0, 1, 2, … |
| `∀ a b : ℕ, …` | for all natural numbers `a` and `b` |
| `x ∣ y` | `x` divides `y` |
| `P → Q` | if `P` then `Q` |
| `P ∧ Q` | `P` and `Q` |
| `def f (a b : ℕ) : ℕ := …` | a function from two naturals to a natural |
| `if h : c then … else …` | an `if` that names the condition `h` |
| `a / b`, `a % b` on `ℕ` | division rounding down, remainder |
| `termination_by m` | "the value `m` gets smaller in every recursive call" |
| `theorem name (a b : ℕ) : claim` | a named, proved claim |
| `example : claim := proof` | an unnamed claim for Lean to check |
| `#guard e` | fail the build unless `e` is true |
| `ℕ × ℕ`, `p.1`, `p.2` | a pair and its two parts |
| `let r := e` | give the value `e` the name `r` |
| `Nat.size n` | the number of bits in `n` |
| `sorry` | a missing proof |

## Proof tactics in this chapter (optional)

These appear only in the "Show and explain the proof" sections.

| You'll see | It means |
| :--- | :--- |
| `:= by …` | a proof written as tactics, each one changing the goal until nothing is left |
| `induction a, b using f.induct with` | induction with one case per branch of `f`; recursive cases get `ih` |
| `ih` | the induction hypothesis: the claim already holds for the recursive call |
| `f.eq_def` | the equation that unfolds `f` into its definition |
| `rw [h₁, h₂]` | rewrite the goal with each equation in turn |
| `dif_pos h`, `dif_neg h` | pick the `then` / `else` branch of `if h : c`, given a proof that `c` holds / doesn't |
| `exact p` | "`p` is the proof" |
| `h.symm` | `h` with its two sides swapped |
| `have h : P := …` | prove an intermediate fact `P` and call it `h` (unnamed: `this`) |
| `omega` | prove facts about `+`, `−`, `≤` and multiplication by fixed numbers |
| `all_goals t` | run `t` on every remaining goal |
| `conv_lhs => rw [h]` | rewrite only the left-hand side of the goal |
| `(by omega)` | a small proof written inline, where an argument is expected |
