# Formalization of Euclidean GCD Complexity and Mathlib Asymptotics Bridge

This document details the formalization of step counting and logarithmic upper bounds
for the standard Euclidean algorithm (`Nat.gcd`) and the connection of both Binary GCD
and Euclidean GCD complexity bounds to Mathlib's `Asymptotics.IsBigO` framework.

---

## 1. Architectural Overview

The repository architecture expands to four cohesive modules under `Amort/GCD/`:

```
Amort/
├── Amort.lean               -- Root library export
└── GCD/
    ├── BinaryGCD.lean       -- Stein's algorithm, termination, invariant DAG, Nat.gcd equivalence
    ├── StepCount.lean       -- Binary GCD step counter, instrumented (gcd, steps), bit-size bounds
    ├── EuclideanGCD.lean    -- Euclidean GCD step counter, modulo halving, logarithmic bounds
    ├── Asymptotics.lean     -- Bridge connecting concrete step bounds to Mathlib Asymptotics.IsBigO
    ├── BinaryGCD.md         -- Documentation for Binary GCD formalization
    └── EuclideanAndAsymptotics.md -- Documentation for Euclidean bounds & asymptotics bridge
```

The master entrypoint `Amort.lean` exports all four modules.

---

## 2. Standard Euclidean GCD Step Counting & Upper Bound (R1)

### Definition & Termination
Lean 4 defines `Nat.gcd` with the core recursion:
```lean
Nat.gcd.eq_def (m n : Nat) : m.gcd n = if m = 0 then n else (n % m).gcd m
```
To mirror this computational structure faithfully, `Nat.euclideanGcdSteps` is defined as:
```lean
def euclideanGcdSteps (a b : ℕ) : ℕ :=
  if ha : a = 0 then 0
  else 1 + euclideanGcdSteps (b % a) a
termination_by a
decreasing_by
  exact Nat.mod_lt b (Nat.pos_of_ne_zero ha)
```
Termination is guaranteed because the first argument decreases strictly on each non-zero call
via `Nat.mod_lt b (Nat.pos_of_ne_zero ha)`.

### Modulo Halving Property
A central property in the complexity analysis of the Euclidean algorithm (first noted by
Émile Lemoine and Gabriel Lamé) is that taking the remainder cuts the larger operand
by more than half whenever the modulus is at most the dividend.

In `Amort/GCD/EuclideanGCD.lean`, this is formalized as:
```lean
lemma mod_two_mul_lt {a b : ℕ} (hb : 0 < b) (hba : b ≤ a) : 2 * (a % b) < a
```
**Proof Idea**: By Euclidean division, $a = b \cdot (a / b) + (a \bmod b)$. Since $b \le a$
and $b > 0$, the quotient $q = a / b \ge 1$:
- If $q = 1$, then $a = b + (a \bmod b)$. Since $a \bmod b < b$, we have
  $2 \cdot (a \bmod b) = (a \bmod b) + (a \bmod b) < b + (a \bmod b) = a$.
- If $q \ge 2$, then $b \cdot q \ge 2b > 2 \cdot (a \bmod b)$, whence $a > 2 \cdot (a \bmod b)$.

As a corollary, the division form is also proven:
```lean
lemma mod_le_div_two {a b : ℕ} (hb : 0 < b) (hba : b ≤ a) : a % b ≤ a / 2
```

### Bit-Length Reduction Under Modulo
Using the property `size (a / 2) + 1 = size a` established in `StepCount.lean`, the halving
inequality directly translates into a strict decrement in bit length:
```lean
lemma size_mod_add_one_le {a b : ℕ} (hb : 0 < b) (hba : b ≤ a) :
    Nat.size (a % b) + 1 ≤ Nat.size a
```

### Logarithmic Upper Bounds
Because every two Euclidean steps compute $a \bmod (b \bmod a)$, the argument strictly halves
every two iterations. Strong well-founded induction on $a$ establishes the tighter bound
when $a \le b$:
```lean
lemma euclideanGcdSteps_le_two_mul_size_of_le (a : ℕ) :
    ∀ b, a ≤ b → euclideanGcdSteps a b ≤ 2 * Nat.size a
```
From this intermediate lemma, the general milestone theorems follow immediately:
```lean
theorem euclideanGcdSteps_le_two_mul_size_min (a b : ℕ) :
    euclideanGcdSteps a b ≤ 2 * Nat.size (min a b) + 1

theorem euclideanGcdSteps_le_two_mul_size_add (a b : ℕ) :
    euclideanGcdSteps a b ≤ 2 * Nat.size (a + b) + 1
```

---

## 3. Asymptotics Bridge to Mathlib `IsBigO` (R2)

Mathlib provides asymptotic complexity relations in `Mathlib.Analysis.Asymptotics.Defs`:
- `f =O[l] g` denotes `Asymptotics.IsBigO l f g`, which unfolds to
  $\exists c, \forall^{\mathcal{F}} x \text{ in } l, \|f(x)\| \le c \cdot \|g(x)\|$.

### Universal Bounds for Arbitrary Filters
Because `binaryGcdSteps a b ≤ 2 * Nat.size (a + b)` holds everywhere on $\mathbb{N} \times \mathbb{N}$,
the condition $\|f(x)\| \le 2 \cdot \|g(x)\|$ holds pointwise with constant $c = 2$.
Consequently, `IsBigO` holds for **any** filter $l$:
```lean
theorem isBigO_binaryGcdSteps_size_add (l : Filter (ℕ × ℕ)) :
    (fun p : ℕ × ℕ ↦ ((binaryGcdSteps p.1 p.2 : ℕ) : ℝ)) =O[l]
    (fun p : ℕ × ℕ ↦ ((Nat.size (p.1 + p.2) : ℕ) : ℝ))

theorem isBigO_binaryGcdSteps_size_add_size (l : Filter (ℕ × ℕ)) :
    (fun p : ℕ × ℕ ↦ ((binaryGcdSteps p.1 p.2 : ℕ) : ℝ)) =O[l]
    (fun p : ℕ × ℕ ↦ ((Nat.size p.1 + Nat.size p.2 : ℕ) : ℝ))
```

### Idiomatic Specializations on `atTop` and Combined Measures
Specializations are provided for the canonical filters used in algorithmic analysis:
1. **`Filter.atTop` on `ℕ × ℕ`**:
   ```lean
   theorem isBigO_binaryGcdSteps_atTop :
       (fun p : ℕ × ℕ ↦ ((binaryGcdSteps p.1 p.2 : ℕ) : ℝ)) =O[Filter.atTop]
       (fun p : ℕ × ℕ ↦ ((Nat.size (p.1 + p.2) : ℕ) : ℝ))
   ```
2. **Pullback filter along the sum measure $a + b$**:
   ```lean
   theorem isBigO_binaryGcdSteps_comap_add_atTop :
       (fun p : ℕ × ℕ ↦ ((binaryGcdSteps p.1 p.2 : ℕ) : ℝ)) =O[
         Filter.comap (fun p ↦ p.1 + p.2) Filter.atTop]
       (fun p : ℕ × ℕ ↦ ((Nat.size (p.1 + p.2) : ℕ) : ℝ))
   ```
3. **Pullback filter along the bit-length measure $\text{size}(a + b)$**:
   ```lean
   theorem isBigO_binaryGcdSteps_comap_size_atTop :
       (fun p : ℕ × ℕ ↦ ((binaryGcdSteps p.1 p.2 : ℕ) : ℝ)) =O[
         Filter.comap (fun p ↦ Nat.size (p.1 + p.2)) Filter.atTop]
       (fun p : ℕ × ℕ ↦ ((Nat.size (p.1 + p.2) : ℕ) : ℝ))
   ```
4. **Instrumented representation equivalence**:
   ```lean
   theorem isBigO_binaryGcdWithSteps_snd_size_add (l : Filter (ℕ × ℕ)) :
       (fun p : ℕ × ℕ ↦ (((binaryGcdWithSteps p.1 p.2).2 : ℕ) : ℝ)) =O[l]
       (fun p : ℕ × ℕ ↦ ((Nat.size (p.1 + p.2) : ℕ) : ℝ))
   ```

### Euclidean GCD Asymptotics
For Euclidean GCD, since `euclideanGcdSteps a b ≤ 2 * Nat.size (min a b) + 1`, once
$\min(a, b) \ge 1$ (which holds eventually under `Filter.atTop` or under `Filter.comap`
towards $\infty$), the $+ 1$ additive constant is absorbed by $1 \le \text{size}(\min a b)$,
yielding a constant $c = 3$:
```lean
theorem isBigO_euclideanGcdSteps_atTop :
    (fun p : ℕ × ℕ ↦ ((euclideanGcdSteps p.1 p.2 : ℕ) : ℝ)) =O[Filter.atTop]
    (fun p : ℕ × ℕ ↦ ((Nat.size (min p.1 p.2) : ℕ) : ℝ))

theorem isBigO_euclideanGcdSteps_comap_min_atTop :
    (fun p : ℕ × ℕ ↦ ((euclideanGcdSteps p.1 p.2 : ℕ) : ℝ)) =O[
      Filter.comap (fun p ↦ min p.1 p.2) Filter.atTop]
    (fun p : ℕ × ℕ ↦ ((Nat.size (min p.1 p.2) : ℕ) : ℝ))

theorem isBigO_euclideanGcdSteps_comap_add_atTop :
    (fun p : ℕ × ℕ ↦ ((euclideanGcdSteps p.1 p.2 : ℕ) : ℝ)) =O[
      Filter.comap (fun p ↦ p.1 + p.2) Filter.atTop]
    (fun p : ℕ × ℕ ↦ ((Nat.size (p.1 + p.2) : ℕ) : ℝ))
```

---

## 4. Style Guide & Linter Audit (R3)

All code in this library conforms strictly to Mathlib standards:
1. **Scoping**: Scoped cleanly under `namespace Nat` (with `open Asymptotics` in `Asymptotics.lean`).
2. **Classification**:
   - `lemma` is used for all intermediate/helper results (`mod_two_mul_lt`, `size_mod_add_one_le`, etc.).
   - `theorem` is used for public milestones (`euclideanGcdSteps_le_two_mul_size_min`, `isBigO_*`).
3. **Docstrings**: Fully documented using `/-- ... -/` docstrings with no assignment tags.
4. **Line Length**: Every line is strictly $\le 100$ characters.
5. **Axiom Verification**: Audited via `#print axioms`. Every theorem relies only on standard Lean axioms:
   - `propext`
   - `Classical.choice`
   - `Quot.sound`
   Zero reliance on `sorryAx`.

---

## 5. Build and Verification Integrity (R4)

Building with `lake build` executes cleanly:
```bash
$ lake build
Build completed successfully (1471 jobs).
```
Zero warnings, zero errors.
