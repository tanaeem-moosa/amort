# Fast Modular Exponentiation

*Needs Binary GCD. It doesn't unlock anything yet.*

Computing a^b mod m is at the heart of RSA and Diffie–Hellman, where `b` has hundreds of digits. Multiplying `a` by itself `b` times would never finish. Repeated squaring needs about two multiplications per bit of `b` instead. Like Binary GCD, it works one bit at a time: check whether the number is odd, then halve it.

This chapter's correctness theorem has a condition, `1 < m`. Deciding whether that condition is fair, and whether it's even the right one, is the main exercise.

The companion file is `Tutorial/ModExp.lean`.

## 1. The problem

Given natural numbers `a`, `b` and `m`, compute the remainder of a^b divided by `m`.

- 3^13 = 1,594,323, so 3^13 mod 100 = 23.
- a^0 = 1, so a^0 mod m = 1 mod m, which is 1 unless m = 1.
- m = 0 needs a decision. "Remainder after dividing by 0" has no standard meaning. Lean's convention is that n % 0 = n, but this algorithm returns 0 when m = 0. We'll see what that does to the theorem.

## 2. What "correct" means in Lean

The specification is just the expression `(a ^ b) % m`, using Lean's own `^` and `%`. Lean could compute it directly, by building the full number a^b and then dividing, but for large `b` that number is far too big to build. It's a perfectly good *specification*, though: it says exactly what the answer is, and it has nothing to do with how we'll compute it.

## 3. The algorithm

Keep three numbers: an accumulator `acc`, a `base` and an exponent `exp`. Start with `acc = 1`, `base = a`, `exp = b`. At each step, if `exp` is odd, multiply `acc` by `base`. Then square `base` and halve `exp`. When `exp` reaches 0, `acc` is the answer. Reduce everything mod `m` along the way, so the numbers never grow past m².

Why it works: the product acc × base^exp never changes. When `exp` is even, squaring `base` and halving `exp` leave base^exp the same. When `exp` is odd, one factor of `base` moves into `acc` first. At the start the product is a^b; at the end, exp = 0, so it's `acc`.

In Python:

```python
def mod_exp(a, b, m):
    if m == 0: return 0
    acc, base, exp = 1 % m, a % m, b
    while exp > 0:
        if exp % 2 == 1: acc = acc * base % m
        base = base * base % m
        exp //= 2
    return acc % m
```

In Lean, from `Amort/NumberTheory/ModExp.lean`, the loop becomes a recursive function that passes the three numbers along:

```lean
def modExpAux (m : ℕ) (acc base exp : ℕ) : ℕ :=
  if exp = 0 then
    acc % m
  else
    let acc' := if exp % 2 = 1 then (acc * base) % m else acc
    let base' := (base * base) % m
    modExpAux m acc' base' (exp / 2)
termination_by exp
decreasing_by omega
```

```lean
def modExp (a b m : ℕ) : ℕ :=
  if m = 0 then 0
  else modExpAux m (1 % m) (a % m) b
```

Here is how to read the Lean:

- `(m : ℕ) (acc base exp : ℕ)` are four natural-number inputs. Grouping them in two pairs of brackets is just style.
- `let acc' := if … then … else …` uses `if` as an expression that produces a value, like Python's `x if c else y`. `acc'` is an ordinary name; the `'` is part of it.
- The recursive call is the last thing the function does, with the updated numbers, so it does the same job as one more turn of the `while` loop.
- `termination_by exp` and `decreasing_by omega` prove that `exp` shrinks: `exp / 2 < exp` whenever `exp ≠ 0`.

### Running it

```lean
#guard modExp 3 13 100 = 23
#guard modExp 2 10 1000 = 24
#guard modExp 7 1000000 13 = 9
```

The last one would need a million multiplications done the slow way, and the number 7^1000000 has about 845,000 digits. Repeated squaring does 27 multiplications.

## 4. The correctness theorem

```lean
theorem modExp_correct (a b m : ℕ) (_hm : 1 < m) :
    modExp a b m = (a ^ b) % m := by
```

For any `a` and `b`, and any modulus greater than 1, the algorithm returns the specification.

Is the condition `1 < m` fair? Part of it is necessary. With m = 0 the theorem would be false:

```lean
#guard modExp 5 3 0 = 0
#guard 5 ^ 3 % 0 = 125
```

So some condition has to rule out m = 0, and a condition that rules out an input where the two sides really do disagree is legitimate. It's a statement about the inputs, not an assumption that the answer is right.

But look at what `1 < m` rules out: 0 *and* 1. Does m = 1 need to be excluded? Exercise 2 asks you to decide.

<details>
<summary>Show and explain the proof (optional)</summary>

The proof turns the "the product never changes" argument into an invariant about `modExpAux`. A new piece of notation first: `x ≡ y [MOD m]` means `x` and `y` have the same remainder mod `m` (`Nat.ModEq` in Mathlib). Facts like "if x ≡ y then x × z ≡ y × z" let the proof reduce mod `m` at any step without changing the answer.

```lean
theorem modExpAux_correct (m acc base exp : ℕ) (_hm : 0 < m) :
    modExpAux m acc base exp = (acc * base ^ exp) % m := by
  induction exp using Nat.strong_induction_on generalizing acc base with
  | _ exp ih =>
    unfold modExpAux
    split
    · rename_i hexp0
      subst hexp0
      simp
    · rename_i hexp_ne
      have hexp_pos : 0 < exp := by omega
      have hlt : exp / 2 < exp := by omega
      have hstep := ih (exp / 2) hlt
        (if exp % 2 = 1 then (acc * base) % m else acc) ((base * base) % m)
      rw [hstep]
      have hmodeq := modExp_step_modEq m acc base exp
      exact hmodeq
```

- The statement *is* the invariant: whatever `acc`, `base` and `exp` the loop is at, it returns (acc × base^exp) mod m. It holds for every state, not just the starting one, which is what makes induction work.
- `generalizing acc base` is needed because the recursive call has different `acc` and `base`.
- `unfold modExpAux` unfolds one step, and `split` splits on `if exp = 0`. `rename_i` names the condition of each branch, which `split` leaves unnamed.
- Base case: `subst hexp0` replaces `exp` with 0 everywhere, and `simp` finishes, since base^0 = 1.
- Step: the induction hypothesis turns the recursive call into ((acc′) × (base′)^(exp / 2)) mod m. What's left is that this equals (acc × base^exp) mod m, and that's exactly the lemma `modExp_step_modEq`, the "one step doesn't change the product" fact with the reductions mod `m` included. Its proof does the algebra (squaring and halving, `mod_step_algebra`) and the reductions (`Nat.ModEq.mul`, `Nat.ModEq.pow`) separately.

The hypothesis `_hm : 0 < m` has an underscore: the proof never uses it. As in the Euclid chapter, that's a hint that the theorem would also hold without it.

The headline theorem then plugs in the starting state:

```lean
theorem modExp_correct (a b m : ℕ) (_hm : 1 < m) :
    modExp a b m = (a ^ b) % m := by
  unfold modExp
  have hm0 : m ≠ 0 := by omega
  simp only [hm0, ite_false]
  have hm_pos : 0 < m := by omega
  rw [modExpAux_correct m (1 % m) (a % m) b hm_pos]
  have h1 : 1 % m ≡ 1 [MOD m] := Nat.mod_modEq 1 m
  have ha : a % m ≡ a [MOD m] := Nat.mod_modEq a m
  have hpow : (a % m) ^ b ≡ a ^ b [MOD m] := Nat.ModEq.pow b ha
  have hmul : (1 % m) * (a % m) ^ b ≡ 1 * a ^ b [MOD m] := Nat.ModEq.mul h1 hpow
  rw [one_mul] at hmul
  exact hmul
```

- `simp only [hm0, ite_false]` uses `m ≠ 0` to throw away the `if m = 0` branch of `modExp`.
- After applying the invariant, the goal is ((1 % m) × (a % m)^b) % m = a^b % m. The `have`s build it from Mathlib facts: reducing mod `m` doesn't change a number's remainder (`Nat.mod_modEq`), and that survives powers and products.
- `hm0` and `hm_pos` are the only places `_hm` is used, and both need only m ≠ 0.

</details>

## 5. How many multiplications

We count multiplications: one squaring per step, plus one more when `exp` is odd. The cost per step is therefore 1 or 2, depending on the current bit.

```lean
theorem modExpWithCount_fst (a b m : ℕ) :
    (modExpWithCount a b m).1 = modExp a b m := by
```

```lean
theorem modExpWithCount_snd_le (a b m : ℕ) :
    (modExpWithCount a b m).2 ≤ 2 * Nat.size b := by
```

At most two multiplications per bit of the exponent. For a 2048-bit exponent, as in RSA, that's at most 4096 multiplications, instead of a number of them with over 600 digits.

```lean
#guard modExpWithCount 3 13 100 = (23, 7)
#guard modExpWithCount 7 1000000 13 = (9, 27)
```

13 is `1101` in binary. Reading from the lowest bit, the steps cost 2, 1, 2, 2, which is 7, under the bound of 2 × 4 = 8.

What's not counted is the cost of each multiplication. Every number involved is below `m`, so a multiplication's cost depends on how many bits `m` has, and for cryptographic sizes that's far from constant. The theorem counts multiplications, and that's what it says.

<details>
<summary>Show and explain the proof (optional)</summary>

```lean
theorem modExpWithCount_snd_le (a b m : ℕ) :
    (modExpWithCount a b m).2 ≤ 2 * Nat.size b := by
  dsimp [modExpWithCount]
  split_ifs with hm
  · omega
  · rw [modExpAuxWithCount_snd]
    exact modExpMulSteps_le b
```

When m = 0 nothing is computed and the count is 0. Otherwise the count is swapped for `modExpMulSteps b`, a function that only counts (`modExpAuxWithCount_snd` proves they agree), and that is bounded by:

```lean
theorem modExpMulSteps_le (b : ℕ) :
    modExpMulSteps b ≤ 2 * Nat.size b := by
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    cases b with
    | zero =>
      rw [modExpMulSteps]
      simp
    | succ k =>
      rw [modExpMulSteps]
      have hpos : 0 < k + 1 := by omega
      have hlt : (k + 1) / 2 < k + 1 := by omega
      have hrec := ih ((k + 1) / 2) hlt
      have hsize : Nat.size ((k + 1) / 2) = Nat.size (k + 1) - 1 :=
        Amort.Recurrence.size_div_two (k + 1)
      have hpos_size : 1 ≤ Nat.size (k + 1) := Nat.size_pos.mpr hpos
      have hmults : (if (k + 1) % 2 = 1 then 2 else 1) ≤ 2 := by
        split <;> omega
      omega
```

This is the same argument as Binary GCD's bound. Each step costs at most 2 (`hmults`) and removes one bit (`hsize`), and the induction hypothesis covers the rest. `split <;> omega` splits the `if` and runs `omega` on both branches: `t₁ <;> t₂` means "do `t₁`, then do `t₂` on every goal it produces".

</details>

## Spot the fake

### "modExp is correct"

All options compile; the companion file has them.

**Option A**

```lean
theorem modExp_correct (a b m : ℕ) (_hm : 1 < m) :
    modExp a b m = (a ^ b) % m := by
```

**Option B**

```lean
theorem modExp_lt (a b m : ℕ) (hm : 0 < m) : modExp a b m < m := by
```

**Option C**

```lean
def powMod (a b m : ℕ) : ℕ := modExp a b m
```

```lean
theorem modExp_eq_powMod (a b m : ℕ) : modExp a b m = powMod a b m := rfl
```

<details>
<summary>Show answer</summary>

A.

B says the answer is a remainder mod `m`. That's true of every function that ends with `% m`, including one that always returns 0. It doesn't say *which* remainder.

C has no conditions at all, which can look stronger than A. But `powMod` isn't a specification: it's `modExp` under another name, so the theorem says the algorithm equals itself. A name like `powMod` suggests "the power, mod m", and that suggestion is all the theorem has going for it. Always look at the definition behind a name on the right-hand side.

A's condition `1 < m` is about the inputs, and it rules out m = 0, where the two sides really differ. A condition isn't a flaw in itself; the question is whether it assumes something it shouldn't.

</details>

## Exercises

**1. Predict.** What does `#eval modExpWithCount 2 10 1000` print?

<details>
<summary>Show answer</summary>

`(24, 6)`. 2^10 = 1024, and 1024 mod 1000 = 24. 10 is `1010` in binary, so reading from the lowest bit the steps cost 1, 2, 1, 2, which is 6.

</details>

**2. State it yourself.** `modExp_correct` assumes `1 < m`. Write the strongest correctness statement you can: what is the weakest condition on `m` that still makes it true?

<details>
<summary>Show answer</summary>

```lean
theorem modExp_correct_of_pos (a b m : ℕ) (hm : 0 < m) :
    modExp a b m = (a ^ b) % m := by
```

m = 1 is fine: everything mod 1 is 0, and `modExp` returns 0. Only m = 0 has to go. So `0 < m` is enough, and `modExp_correct` with `1 < m` is slightly weaker than it could be. It says nothing about m = 1. The companion file proves this stronger version, with a proof only a little different from the original.

This is the same lesson as the unused `_ha` in the Euclid chapter, from the other side. The repository's own proof only ever used `m ≠ 0` (look at `hm0` and `hm_pos` in the optional proof section), which was the hint that `1 < m` asked for more than necessary.

</details>

**3. Prove it with AI.**

```lean
-- exercise
theorem modExp_zero_exp (a m : ℕ) (hm : 0 < m) : modExp a 0 m = 1 % m := by
  sorry
```

Before asking for a proof, decide whether the condition `hm` is needed. (Hint: what are `modExp a 0 0` and `1 % 0`?) Then paste the statement at the end of the companion file, ask an assistant for a proof, and build.

## Lean introduced in this chapter

| You'll see | It means |
| :--- | :--- |
| `a ^ b` | `a` to the power `b` |
| `n % 0 = n` | Lean's convention for the remainder mod 0 |
| `let x' := if c then e₁ else e₂` | an `if` that produces a value |
| `x ≡ y [MOD m]` | `x` and `y` have the same remainder mod `m` (`Nat.ModEq`) |

## Proof tactics in this chapter (optional)

New ones from the "Show and explain the proof" sections.

| You'll see | It means |
| :--- | :--- |
| `unfold f` | unfold one step of the definition of `f` |
| `split` | split on the `if` in the goal (here, inside `modExpAux`) |
| `rename_i h` | name the latest unnamed hypothesis `h` |
| `subst h` | given `h : x = e`, replace `x` with `e` everywhere |
| `simp only [h, ite_false]` | simplify an `if` whose condition `h` shows is false |
| `Nat.ModEq.mul`, `Nat.ModEq.pow` | `≡` survives multiplication and powers |
| `t₁ <;> t₂` | run `t₁`, then `t₂` on every goal it produces |
