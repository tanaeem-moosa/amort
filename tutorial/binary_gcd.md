# 🌱 Binary GCD (Stein's Algorithm)

> **Skill Tree Tier 1 | Opening Node**  
> **Prerequisites:** None (Root Node)  
> **Unlocks:** Euclid's GCD (`EUC`), Insertion Sort (`INS`), Binary Search (`BS`), Dynamic Array (`DYN`), Fast Modular Exponentiation (`MODEXP`)  
> **Companion Lean File:** `Tutorial/BinaryGCD.lean`  
> **Reference Modules:** `Amort.GCD.BinaryGCD`, `Amort.GCD.StepCount`  
> **Headline Theorems:** `Nat.binaryGcd_eq_gcd`, `Nat.binaryGcdWithSteps_fst`, `Nat.binaryGcdWithSteps_snd_le_size_add_size`, `Nat.binaryGcdWithSteps_snd_le_two_mul_size_add`, `Nat.isBigO_binaryGcdSteps_atTop`

---

## The Big Idea

When AI writes the code, **understanding becomes the job**.

An AI code assistant can produce a 50-line algorithm, attach a docstring saying *"formally verified in Lean 4"*, and return a green compilation check in seconds. But does the theorem actually guarantee what you think it guarantees? Or does it secretly prove a trivial tautology?

In this curriculum, the division of labour is absolute:
- **You own the statement.**
- **The AI writes the proof.**
- **Lean referees.**

We begin with **Stein's Binary GCD Algorithm** (1967). It is the perfect opening node: it operates directly on natural numbers (`ℕ`), requires no advanced data structures, replaces expensive multi-word division with elementary bit shifts and subtractions, and highlights the foundational distinction between **numeric value** ($n$) and **bit length** ($\approx \log_2 n$).

---

## Step 1: Define the Problem

The Greatest Common Divisor (GCD) of two natural numbers $a$ and $b$ is the largest natural number $d$ that divides both $a$ and $b$ without a remainder ($d \mid a$ and $d \mid b$).

### Concrete Examples
- $\gcd(48, 18) = 6$, because the divisors of 48 are $\{1, 2, 3, 4, 6, 8, 12, 16, 24, 48\}$, the divisors of 18 are $\{1, 2, 3, 6, 9, 18\}$, and their common divisors are $\{1, 2, 3, 6\}$.
- $\gcd(105, 252) = 21$.
- $\gcd(7, 13) = 1$ (coprime numbers).

### Edge Cases
1. **Zero as one argument:**
   $$\gcd(a, 0) = a \quad \text{and} \quad \gcd(0, b) = b$$
   Every natural number divides 0 ($d \cdot 0 = 0$), so the greatest divisor shared by $a$ and 0 is simply $a$ itself.
2. **Both arguments zero:**
   $$\gcd(0, 0) = 0$$
   By standard mathematical convention in $\mathbb{N}$ (and in Mathlib's divisibility lattice), 0 is the universal multiple. Defining $\gcd(0, 0) = 0$ preserves the algebraic law that $d \mid 0$ for all $d$.

---

## Step 2: Formalize the Definition

Before examining any algorithmic implementation, how do we write down what a "correct GCD" is in Lean 4?

We specify the problem using Mathlib's canonical definition `Nat.gcd a b`. In Lean's number theory library, `Nat.gcd` is characterized by three fundamental properties:

```lean
-- 1. It is a common divisor:
Nat.gcd_dvd_left  : ∀ (a b : ℕ), Nat.gcd a b ∣ a
Nat.gcd_dvd_right : ∀ (a b : ℕ), Nat.gcd a b ∣ b

-- 2. It is the greatest common divisor in the divisibility order:
Nat.dvd_gcd : ∀ {a b k : ℕ}, k ∣ a → k ∣ b → k ∣ Nat.gcd a b
```

Notice what is **not** here: there is no mention of loops, bit shifts, divisions, or execution counters. This is an **independent specification**. Any valid GCD algorithm—whether Stein's binary algorithm, Euclid's remainder algorithm, or a brute-force search—must produce an output identical to `Nat.gcd a b`.

---

## Step 3: Understand the Algorithm

Classical Euclidean division computes $a \bmod b$, which requires hardware or multi-word division. Josef Stein (1967) observed that on binary computers, division by 2 is a single-cycle bit shift (`>> 1`) and parity testing is a bitwise AND (`a & 1 == 0`).

Stein's algorithm relies on three arithmetic identities:
1. **Both Even:** If $a$ and $b$ are even, $\gcd(a, b) = 2 \cdot \gcd(a / 2, b / 2)$.
2. **One Even, One Odd:** If $a$ is even and $b$ is odd, $\gcd(a, b) = \gcd(a / 2, b)$ (since 2 cannot divide an odd number $b$).
3. **Both Odd:** If both $a$ and $b$ are odd and $b \le a$, then their difference $a - b$ is **even**! Therefore:
   $$\gcd(a, b) = \gcd(a - b, b) = \gcd((a - b) / 2, b)$$

### Lean 4 Implementation

Here is the verified implementation from `Amort/GCD/BinaryGCD.lean`:

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

### Running the Algorithm in Lean

Open `Tutorial/BinaryGCD.lean` and execute `#eval`:

```lean
#eval Nat.binaryGcd 48 18     -- 6
#eval Nat.binaryGcd 105 252   -- 21
#eval Nat.binaryGcd 0 7       -- 7
#eval Nat.binaryGcd 0 0       -- 0
```

### Why Does It Terminate? (`termination_by a + b`)
In Lean 4, all functions must be proven total. The clause `termination_by a + b` specifies the **well-founded termination measure**: the sum of the inputs strictly decreases across every recursive branch:
- If both are even: $(a / 2) + (b / 2) \le (a + b) / 2 < a + b$ (since $a, b > 0$).
- If one is even: $(a / 2) + b < a + b$ (since $a \ge 2$).
- If both are odd and $b \le a$: $((a - b) / 2) + b = (a + b) / 2 < a + b$ (since $b \ge 1$).

Because a natural number cannot decrease infinitely, the algorithm is guaranteed to terminate.

---

## Step 4: State Correctness

We must verify that `binaryGcd` computes the exact greatest common divisor for **all** inputs:

```lean
@[simp]
theorem binaryGcd_eq_gcd (a b : ℕ) : binaryGcd a b = Nat.gcd a b
```

### How to Read This Statement
- **Universality:** `∀ (a b : ℕ)` means there are **no preconditions**. No assumptions that $a > 0$, that $a \ne b$, or that inputs are already reduced.
- **Equality to Canonical Spec:** The right-hand side is `Nat.gcd a b`, tying the algorithm directly to Mathlib's verified number theory specification.

### Proof Idea: The Lemma Invariant DAG
The proof proceeds by induction on `a, b using binaryGcd.induct`. At each branch, Lean verifies an invariant lemma:
1. `coprime_two_of_odd`: If $b \% 2 = 1$, then $\gcd(2, b) = 1$.
2. `gcd_even_odd`: If $a$ is even and $b$ is odd, $\gcd(a, b) = \gcd(a / 2, b)$.
3. `gcd_even_even`: If both are even, $\gcd(a, b) = 2 \cdot \gcd(a / 2, b / 2)$.
4. `gcd_odd_odd_sub_div_two_left`: If both are odd and $b \le a$, $\gcd(a, b) = \gcd((a - b) / 2, b)$.

Because each recursive branch preserves the GCD, the returned base value is the true GCD.

---

## Step 5: State Time Complexity

How many operations does Stein's algorithm perform?
In algorithmic complexity, we count **recursive transitions** (each step is an $O(1)$ bit test, shift, or subtraction).

### The Instrument Coupling Pattern
To prove an honest complexity bound, we must not bound an arbitrary mathematical formula. We must bound the **actual execution** of the algorithm. We use the instrumented function `binaryGcdWithSteps`:

```lean
def binaryGcdWithSteps (a b : ℕ) : ℕ × ℕ := ...
```

This returns `(result_gcd, step_count)`. To prove the count is genuine, we enforce two **coupling theorems**:

```lean
-- 1. The result component matches the verified algorithm:
theorem binaryGcdWithSteps_fst (a b : ℕ) :
    (binaryGcdWithSteps a b).1 = binaryGcd a b

-- 2. The count component matches the recursive step counter:
theorem binaryGcdWithSteps_snd (a b : ℕ) :
    (binaryGcdWithSteps a b).2 = binaryGcdSteps a b
```

### Logarithmic Upper Bound in Bit Length (`Nat.size`)
How fast does it terminate? The headline complexity theorem in `Amort/GCD/StepCount.lean` proves:

```lean
theorem binaryGcdSteps_le_size_add_size (a b : ℕ) :
    binaryGcdSteps a b ≤ Nat.size a + Nat.size b
```

And in combined form:
```lean
theorem binaryGcdWithSteps_snd_le_two_mul_size_add (a b : ℕ) :
    (binaryGcdWithSteps a b).2 ≤ 2 * Nat.size (a + b)
```

### What is `Nat.size`?
In Lean 4, `Nat.size n` is the number of binary bits needed to represent $n$:
$$\text{Nat.size}(n) = \begin{cases} 0 & \text{if } n = 0 \\ \lfloor \log_2 n \rfloor + 1 & \text{if } n > 0 \end{cases}$$

Therefore, `binaryGcdSteps a b ≤ Nat.size a + Nat.size b` proves that the step count is **linear in the number of input bits**, which is **logarithmic in numeric value**:
$$\text{Steps} \le \log_2(a) + \log_2(b) + 2$$

Mathlib's asymptotic notation in `Amort/GCD/Asymptotics.lean` formalizes this:
```lean
theorem isBigO_binaryGcdSteps_atTop :
    (fun p : ℕ × ℕ ↦ (binaryGcdSteps p.1 p.2 : ℝ)) =O[Filter.atTop]
    (fun p : ℕ × ℕ ↦ (Nat.size (p.1 + p.2) : ℝ))
```

---

## 🎯 Spot the Fake

A code assistant presents you with three theorem statements claiming to establish the time complexity of Binary GCD. Which one is genuine?

### Statement A (Circular Formula / Stand-in Anti-Pattern A1)
```lean
def gcdCost (a b : ℕ) : ℕ := Nat.size a + Nat.size b

theorem gcdCost_le (a b : ℕ) :
    gcdCost a b ≤ Nat.size a + Nat.size b := by
  rfl
```
> **Verdict: FAKE.**  
> This theorem compiles with 0 errors! But it is a circular tautology. It defines `gcdCost` as its own bound and proves `X ≤ X`. It has zero connection to `binaryGcd` or any algorithm execution.

### Statement B (Genuine Coupled Bit Complexity)
```lean
theorem binaryGcdWithSteps_fst (a b : ℕ) :
    (binaryGcdWithSteps a b).1 = binaryGcd a b

theorem binaryGcdSteps_le_size_add_size (a b : ℕ) :
    binaryGcdSteps a b ≤ Nat.size a + Nat.size b
```
> **Verdict: GENUINE.**  
> The first theorem couples the instrumented tuple to the actual executable function. The second proves that the instrumented step count is bounded by the sum of the input bit lengths.

### Statement C (Value-Linear Weak Bound)
```lean
theorem binaryGcdSteps_le_val_add (a b : ℕ) :
    binaryGcdSteps a b ≤ a + b
```
> **Verdict: WEAK / MISLEADING.**  
> This theorem is true and coupled to `binaryGcdSteps`. However, bounding by $a + b$ is **linear in numeric value**, which is **exponential** in input bit length ($2^k$). It completely misses the logarithmic efficiency of Stein's algorithm.

---

## 🧪 Interactive Exercises

### 1. Predict
Test your mental execution of Stein's algorithm:

1. **Question 1:** What does `#eval binaryGcd 48 18` evaluate to?
   - *Expected Answer:* `6`
   - *Trace:* $\gcd(48, 18) = 2 \cdot \gcd(24, 9) = 2 \cdot \gcd(12, 9) = 2 \cdot \gcd(6, 9) = 2 \cdot \gcd(3, 9) = 2 \cdot \gcd(3, (9-3)/2) = 2 \cdot \gcd(3, 3) = 2 \cdot 3 = 6$.
2. **Question 2:** What does `#eval binaryGcd 0 7` evaluate to?
   - *Expected Answer:* `7`
   - *Explanation:* When $a = 0$, the algorithm immediately returns $b$.

### 2. State It Yourself
In `Tutorial/BinaryGCD.lean`, write and check these statements:

```lean
/-- Commutativity of Binary GCD -/
example (a b : ℕ) : Nat.binaryGcd a b = Nat.binaryGcd b a := by
  rw [Nat.binaryGcd_eq_gcd, Nat.binaryGcd_eq_gcd, Nat.gcd_comm]

/-- Factoring out 2 when both are even -/
example (a b : ℕ) (ha : a % 2 = 0) (hb : b % 2 = 0) :
    Nat.binaryGcd a b = 2 * Nat.binaryGcd (a / 2) (b / 2) := by
  rw [Nat.binaryGcd_eq_gcd, Nat.binaryGcd_eq_gcd]
  exact Nat.gcd_even_even ha hb
```

### 3. Prove It with AI
Copy this theorem statement into an AI chat:
```lean
theorem binaryGcd_zero_right (a : ℕ) : Nat.binaryGcd a 0 = a
```
Ask the AI: *"Provide a Lean 4 proof for this theorem using `Nat.binaryGcd_eq_gcd`."*  
Then paste the proof into `Tutorial/BinaryGCD.lean` and let Lean verify it. Notice how easy verification is once the statement is crystal clear!
