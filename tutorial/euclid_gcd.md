# 🏛️ Euclid's GCD

> **Skill Tree Tier 2 | Arithmetic & Number Theory**  
> **Prerequisites:** Binary GCD (`BGCD`)  
> **Unlocks:** Extended Euclid & Bézout (`EXT`)  
> **Companion Lean File:** `Tutorial/EuclideanGCD.lean`  
> **Reference Module:** `Amort.GCD.EuclideanGCD`  
> **Headline Theorems:** `Nat.euclidGcd_eq_gcd`, `Nat.euclidGcdWithSteps_fst`, `Nat.euclidGcdWithSteps_snd`, `Nat.euclidGcdWithSteps_snd_le_two_mul_size_min`, `Nat.euclidGcdWithSteps_snd_le_two_mul_size_add`, `Nat.isBigO_euclidGcdWithSteps_snd_atTop`

---

## The Big Idea

In the previous node ([Binary GCD](binary_gcd.md)), we formalized Stein's bitwise algorithm. Now, we explore the classical **Euclidean Algorithm** (c. 300 BCE).

This chapter introduces one of the most profound principles in formal software verification:
> **One Specification, Multiple Algorithms.**

Two algorithms can have completely different execution strategies, recurrences, and cost profiles, yet be proven **mathematically identical** because they both satisfy the exact same canonical specification (`Nat.gcd a b`). Furthermore, we will prove **cross-algorithm equivalence**:
$$\text{euclidGcd}(a, b) = \text{binaryGcd}(a, b)$$

---

## Step 1: Define the Problem

Given two natural numbers $a, b \in \mathbb{N}$, find the greatest common divisor $\gcd(a, b)$ using repeated Euclidean division (remainders).

### The Euclidean Reduction Rule
If $a > 0$, any common divisor of $a$ and $b$ must also divide the remainder $b \bmod a$, because:
$$b = q \cdot a + (b \bmod a) \implies (b \bmod a) = b - q \cdot a$$
If $d \mid a$ and $d \mid b$, then $d$ divides any linear combination of $a$ and $b$. Therefore:
$$\gcd(a, b) = \gcd(b \bmod a, a)$$

When $a$ reaches $0$, the reduction stops and returns $b$:
$$\gcd(0, b) = b$$

### Contrast: Euclid vs. Stein
- **Euclidean GCD:** Shrinks arguments dramatically in each step using integer division and modulo (`%`).
- **Binary GCD:** Avoids multi-word division by using single-bit shifts (`>> 1`) and subtractions.

---

## Step 2: Formalize the Definition

Euclidean GCD targets the exact same specification as Binary GCD: Mathlib's `Nat.gcd a b`.

### The Modulo Halving Invariant
Why is Euclidean GCD fast? Because taking the remainder with respect to a smaller number at least **halves** the argument every two steps! In `Amort/GCD/EuclideanGCD.lean`, this fundamental geometric contraction is proved as:

```lean
lemma mod_two_mul_lt {a b : ℕ} (hb : 0 < b) (hba : b ≤ a) : 2 * (a % b) < a
```

In plain language: whenever $0 < b \le a$, the remainder $a \bmod b$ is strictly less than half of $a$ ($a \bmod b < a / 2$).

---

## Step 3: Understand the Algorithm

Here is the executable definition from `Amort/GCD/EuclideanGCD.lean`:

```lean
def euclidGcd (a b : ℕ) : ℕ :=
  if a = 0 then b
  else euclidGcd (b % a) a
termination_by a
decreasing_by
  exact Nat.mod_lt b (by omega)
```

### Running the Algorithm in Lean

Open `Tutorial/EuclideanGCD.lean` and execute `#eval`:

```lean
#eval Nat.euclidGcd 48 18     -- 6
#eval Nat.euclidGcd 105 252   -- 21
#eval Nat.euclidGcd 0 7       -- 7
#eval Nat.euclidGcd 0 0       -- 0
```

### Step-by-Step Execution Trace on `48` and `18`
1. Call `euclidGcd 48 18`: $a = 48 \ne 0$. Next is `(18 % 48, 48) = (18, 48)`.
2. Call `euclidGcd 18 48`: $a = 18 \ne 0$. Next is `(48 % 18, 18) = (12, 18)`.
3. Call `euclidGcd 12 18`: $a = 12 \ne 0$. Next is `(18 % 12, 12) = (6, 12)`.
4. Call `euclidGcd 6 12`: $a = 6 \ne 0$. Next is `(12 % 6, 6) = (0, 6)`.
5. Call `euclidGcd 0 6`: $a = 0 \implies$ returns `6`.

Notice that if the first argument is larger than the second ($48 > 18$), step 1 acts as an automatic swap via $18 \bmod 48 = 18$.

### Termination Proof (`termination_by a`)
The recursion parameter is `a`. Whenever $a > 0$, the standard mathematical property of modulo (`Nat.mod_lt`) guarantees that:
$$b \bmod a < a$$
Since the next recursive call passes $b \bmod a$ as its first argument, the termination measure strictly decreases at every step.

---

## Step 4: State Correctness

The headline theorem proves that `euclidGcd` computes the exact greatest common divisor for all inputs:

```lean
theorem euclidGcd_eq_gcd (a b : ℕ) : euclidGcd a b = Nat.gcd a b
```

### Cross-Algorithm Equivalence
Because both `euclidGcd` and `binaryGcd` are proven equal to `Nat.gcd`, we can immediately prove that they produce identical results on all inputs:

```lean
theorem euclid_eq_binary (a b : ℕ) : Nat.euclidGcd a b = Nat.binaryGcd a b := by
  rw [Nat.euclidGcd_eq_gcd, Nat.binaryGcd_eq_gcd]
```

This is the power of formal specification: you do not need to construct a complex inductive bisimulation between the bit-shifting logic of Stein and the division logic of Euclid. You simply verify both against `Nat.gcd`, and transitivity gives equivalence for free!

---

## Step 5: State Time Complexity

What are we counting in Euclidean GCD? We count the number of **division/modulo operations** executed.

### The Instrumented Function and Coupling
In `Amort/GCD/EuclideanGCD.lean`, we instrument the algorithm to return `(result_gcd, modulo_count)`:

```lean
def euclidGcdWithSteps (a b : ℕ) : ℕ × ℕ :=
  if a = 0 then (b, 0)
  else
    let (g, s) := euclidGcdWithSteps (b % a) a
    (g, 1 + s)
```

The coupling theorems ensure that the instrumented function is faithful:

```lean
theorem euclidGcdWithSteps_fst (a b : ℕ) : (euclidGcdWithSteps a b).1 = euclidGcd a b
theorem euclidGcdWithSteps_snd (a b : ℕ) : (euclidGcdWithSteps a b).2 = euclideanGcdSteps a b
```

### Logarithmic Upper Bound in the Minimum Input (`min a b`)
Because `2 * (a % b) < a`, the bit length of the remainder decreases by at least 1 every two steps (`Nat.size_mod_add_one_le`). This yields the famous Lamé-style logarithmic upper bound:

```lean
theorem euclidGcdWithSteps_snd_le_two_mul_size_min (a b : ℕ) :
    (euclidGcdWithSteps a b).2 ≤ 2 * Nat.size (min a b) + 1
```

### Why `min a b`?
Notice the elegance of this bound: the number of steps depends **only on the smaller number**! Even if $b$ is a 10,000-bit number, if $a = 6$, the algorithm will finish in at most $2 \cdot \text{size}(6) + 1 = 2 \cdot 3 + 1 = 7$ steps.

### Comparing Operational Step Counts
Let us compare the concrete step counts between Euclid and Binary GCD on `(48, 18)`:
```lean
#eval Nat.euclidGcdWithSteps 48 18    -- (6, 4): 4 modulo operations
#eval Nat.binaryGcdWithSteps 48 18   -- (6, 6): 6 bit transitions
```
Euclid takes fewer steps (4 vs. 6), but each Euclidean step is a full division (`%`), whereas each Binary GCD step is a fast bit shift or subtraction.

---

## 🎯 Spot the Fake

An AI assistant submits three candidate theorem statements to "prove" the correctness of Euclidean GCD. Which one is genuine?

### Statement A (Reflexive Identity / Tautology Anti-Pattern A4)
```lean
theorem euclidGcd_self (a b : ℕ) : euclidGcd a b = euclidGcd a b := by
  rfl
```
> **Verdict: FAKE.**  
> A reflexive identity $f(x) = f(x)$ proves nothing about whether $f$ computes the GCD. Even a completely broken function that returns `42` on all inputs satisfies this statement!

### Statement B (Genuine Full Specification)
```lean
theorem euclidGcd_eq_gcd (a b : ℕ) : euclidGcd a b = Nat.gcd a b
```
> **Verdict: GENUINE.**  
> Equates the algorithm output directly to Mathlib's independently verified `Nat.gcd` specification for all $a, b \in \mathbb{N}$.

### Statement C (One-Sided / Incomplete Specification Anti-Pattern A5)
```lean
theorem euclidGcd_divides (a b : ℕ) : euclidGcd a b ∣ a
```
> **Verdict: INCOMPLETE / FAKE.**  
> Proves only that the output divides $a$. It fails to prove that the output divides $b$, and fails to prove that it is the *greatest* common divisor. A dummy function returning `1` for all inputs satisfies this theorem!

---

## 🧪 Interactive Exercises

### 1. Predict
1. **Question:** What does `#eval euclidGcd 105 252` evaluate to?
   - *Expected Answer:* `21`
   - *Trace:*
     - $252 \bmod 105 = 42$
     - $105 \bmod 42 = 21$
     - $42 \bmod 21 = 0 \implies$ returns `21`.
2. **Predicting Steps:** What does `#eval (euclidGcdWithSteps 105 252).2` evaluate to?
   - *Expected Answer:* `5` (including the initial swap).

### 2. State It Yourself
In `Tutorial/EuclideanGCD.lean`, test this property: when $a$ divides $b$ ($a > 0$), Euclid finishes in a single step!

```lean
/-- When a divides b, (b % a) = 0, so the algorithm returns a immediately. -/
example (a b : ℕ) (ha : 0 < a) (hdiv : a ∣ b) :
    Nat.euclidGcd a b = a := by
  rw [Nat.euclidGcd_eq_gcd]
  exact Nat.gcd_eq_left hdiv
```

### 3. Prove It with AI
Give this theorem to an AI assistant:
```lean
theorem euclidGcd_zero_left (b : ℕ) : Nat.euclidGcd 0 b = b
```
Ask: *"Prove `euclidGcd_zero_left` in Lean 4 by unfolding `Nat.euclidGcd`."*  
Paste the result into `Tutorial/EuclideanGCD.lean` and confirm that Lean accepts it without warnings!
