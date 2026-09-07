# amort

AI-assisted formalization of time complexity and correctness of algorithms in Lean 4.

## Modules Overview

This repository formalizes algorithms and their computational complexity in `Amort/GCD/`:

### 1. Binary GCD (Stein's Algorithm)
- **Formal Definition & Termination**: `Nat.binaryGcd` with well-founded termination measure $a + b$.
- **Mathematical Equivalence**: `Nat.binaryGcd_eq_gcd` proving `∀ a b, binaryGcd a b = Nat.gcd a b`.
- **Step Counting & Bounds**: Companion `Nat.binaryGcdSteps` and instrumented `Nat.binaryGcdWithSteps`:
  - `binaryGcdSteps a b ≤ Nat.size a + Nat.size b`
  - `binaryGcdSteps a b ≤ 2 * Nat.size (a + b)`
- **Documentation**: Detailed architecture, invariant lemma DAG, and proof notes in [`Amort/GCD/BinaryGCD.md`](Amort/GCD/BinaryGCD.md).

### 2. Euclidean GCD Step Counting & Modulo Halving
- **Step Counter**: `Nat.euclideanGcdSteps` mirroring `Nat.gcd.eq_def`.
- **Modulo Halving Property**: `Nat.mod_two_mul_lt` ($2 \cdot (a \bmod b) < a$ when $0 < b \le a$) and bit-size reduction `Nat.size_mod_add_one_le`.
- **Logarithmic Upper Bounds**:
  - `euclideanGcdSteps a b ≤ 2 * Nat.size (min a b) + 1`
  - `euclideanGcdSteps a b ≤ 2 * Nat.size (a + b) + 1`

### 3. Mathlib Asymptotics Bridge (`Asymptotics.IsBigO`)
- **Universal Filters**: `isBigO_binaryGcdSteps_size_add` establishing $O(\text{size}(a + b))$ under arbitrary filters $l$.
- **Canonical Top & Measure Filters**:
  - `isBigO_binaryGcdSteps_atTop` under `Filter.atTop` on `ℕ × ℕ`.
  - `isBigO_binaryGcdSteps_comap_add_atTop` under pullback along $a + b$.
  - `isBigO_binaryGcdSteps_comap_size_atTop` under pullback along $\text{size}(a + b)$.
  - `isBigO_euclideanGcdSteps_atTop` establishing $O(\text{size}(\min a b))$ under `Filter.atTop`.
  - `isBigO_euclideanGcdSteps_comap_min_atTop` under pullback along $\min(a, b)$.
  - `isBigO_euclideanGcdSteps_comap_add_atTop` under pullback along $a + b$.
- **Documentation**: Comprehensive documentation in [`Amort/GCD/EuclideanAndAsymptotics.md`](Amort/GCD/EuclideanAndAsymptotics.md).

## Building and Verification

```bash
lake build
```

Full build executes with 0 warnings and 0 errors across 1471 jobs. All theorems rely exclusively on standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`) with 0 `sorryAx`.

## Disclaimer

This is a personal side project. The views, opinions, and formalizations expressed here are solely those of the author and do not represent or reflect the views, positions, or endorsements of the author's employer (Google LLC). Any rights or intellectual property may be subject to employer agreements, but this project is not an official Google product.
