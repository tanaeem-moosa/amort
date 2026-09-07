# Plan: Binary GCD Formalization in Lean 4

## Overview
Formalize Stein's binary GCD algorithm in Lean 4, prove termination based on argument size/sum, prove mathematical equivalence with `Nat.gcd`, define companion and instrumented step-counting representations with explicit logarithmic upper bounds in terms of bit length, and provide comprehensive documentation.

## Phases & Execution Summary
1. **Phase 1: Architecture & Design** [COMPLETE]
   - Verified Lean 4.33.1 toolchain and Mathlib cache.
   - Designed algorithm using well-founded recursion governed by measure `a + b`.
   - Formulated DAG of auxiliary invariant lemmas for parity, factor-of-2 elimination, and subtraction.

2. **Phase 2: Core Formalization (`Amort/BinaryGCD.lean`)** [COMPLETE]
   - Defined `binaryGcd : ℕ → ℕ → ℕ` with termination proven via `omega`.
   - Proved auxiliary invariant lemmas:
     - `coprime_two_of_odd`: `odd(b) → Nat.Coprime 2 b`
     - `gcd_even_odd`: `even(a) ∧ odd(b) → gcd a b = gcd (a / 2) b`
     - `gcd_odd_even`: `odd(a) ∧ even(b) → gcd a b = gcd a (b / 2)`
     - `gcd_even_even`: `even(a) ∧ even(b) → gcd a b = 2 * gcd (a / 2) (b / 2)`
     - `gcd_odd_odd_sub_div2`: `odd(a) ∧ odd(b) ∧ b ≤ a → gcd a b = gcd ((a - b) / 2) b`
     - `gcd_odd_odd_sub_div2_right`: `odd(a) ∧ odd(b) ∧ a ≤ b → gcd a b = gcd a ((b - a) / 2)`
   - Proved main equivalence theorem: `binaryGcd_eq_gcd : ∀ a b, binaryGcd a b = Nat.gcd a b`.

3. **Phase 3: Step Counting & Bounds (`Amort/StepCount.lean`)** [COMPLETE]
   - Defined companion step counter `binaryGcdSteps (a b : ℕ) : ℕ`.
   - Defined instrumented representation `binaryGcdWithSteps (a b : ℕ) : ℕ × ℕ`.
   - Proved consistency:
     - `binaryGcdWithSteps_fst`: matches `binaryGcd`
     - `binaryGcdWithSteps_snd`: matches `binaryGcdSteps`
     - `binaryGcdWithSteps_eq_gcd`: computes `Nat.gcd`
   - Proved bit size reduction lemmas:
     - `size_div_two`: `0 < a → size (a / 2) + 1 = size a`
     - `size_sub_div_two_le`: `0 < a ∧ 0 < b ∧ b ≤ a → size ((a - b) / 2) + 1 ≤ size a`
   - Proved upper bounds:
     - `binaryGcdSteps_le_size_add_size`: `binaryGcdSteps a b ≤ Nat.size a + Nat.size b`
     - `binaryGcdSteps_le_two_mul_size_add`: `binaryGcdSteps a b ≤ 2 * Nat.size (a + b)`
     - Instrumented step bound mirrors.

4. **Phase 4: Build & Verification Integrity** [COMPLETE]
   - Full `lake build` succeeds with 0 errors and 0 warnings (532 jobs).
   - `#print axioms` verifies zero reliance on `sorryAx` across all theorems.

5. **Phase 5: Documentation & Artifacts** [COMPLETE]
   - Created comprehensive `docs/BinaryGCD.md` with architecture, lemma DAG (Mermaid), step bound analysis, and upstream contribution notes.
   - Updated `README.md` with binary GCD overview and build instructions.
   - Maintained `progress.md`, `plan.md`, and `BRIEFING.md`.
