# amort

AI-assisted formalization of time complexity of various algorithms in Lean 4.

## Binary GCD (Stein's Algorithm)

This repository includes a complete Lean 4 formalization of Stein's binary greatest common divisor algorithm:
- **Formal Definition & Termination**: `Amort.BinaryGCD.binaryGcd` with well-founded termination measure $a + b$.
- **Mathematical Equivalence**: `Amort.BinaryGCD.binaryGcd_eq_gcd` proving `∀ a b, binaryGcd a b = Nat.gcd a b`.
- **Step Counting & Bound**: Companion `binaryGcdSteps` and instrumented `binaryGcdWithSteps` with proven upper bounds:
  - `binaryGcdSteps a b ≤ Nat.size a + Nat.size b`
  - `binaryGcdSteps a b ≤ 2 * Nat.size (a + b)`
- **Documentation**: Detailed architecture, invariant lemma DAG, and proof notes in [`docs/BinaryGCD.md`](docs/BinaryGCD.md).

### Building and Verification
```bash
lake build
```
