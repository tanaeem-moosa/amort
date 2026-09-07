# amort

AI-assisted formalization of time complexity of various algorithms in Lean 4.

## Binary GCD (Stein's Algorithm)

This repository includes a complete Lean 4 formalization of Stein's binary greatest common divisor algorithm located in `Amort/GCD/`:
- **Formal Definition & Termination**: `Nat.binaryGcd` with well-founded termination measure $a + b$.
- **Mathematical Equivalence**: `Nat.binaryGcd_eq_gcd` proving `∀ a b, binaryGcd a b = Nat.gcd a b`.
- **Step Counting & Bound**: Companion `Nat.binaryGcdSteps` and instrumented `Nat.binaryGcdWithSteps` with proven upper bounds:
  - `binaryGcdSteps a b ≤ Nat.size a + Nat.size b`
  - `binaryGcdSteps a b ≤ 2 * Nat.size (a + b)`
- **Documentation**: Detailed architecture, invariant lemma DAG, and proof notes in [`Amort/GCD/BinaryGCD.md`](Amort/GCD/BinaryGCD.md).

### Building and Verification
```bash
lake build
```

## Disclaimer

This is a personal side project. The views, opinions, and formalizations expressed here are solely those of the author and do not represent or reflect the views, positions, or endorsements of the author's employer (Google LLC). Any rights or intellectual property may be subject to employer agreements, but this project is not an official Google product.
