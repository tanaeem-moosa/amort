# Original User Request

## 2026-09-07T18:31:02Z

Formalize binary GCD (Stein's algorithm) in Lean 4, prove termination, verify mathematical equivalence against `Nat.gcd`, formalize step bounds, and document the work.

Working directory: /home/deck/projects/amort
Integrity mode: demo

## Requirements

### R1. Formal Definition and Termination
Define the binary GCD algorithm in Lean 4 over natural numbers with provable termination based on argument size/sum.

### R2. Mathematical Equivalence with Nat.gcd
Prove that the binary GCD implementation is mathematically equivalent to `Nat.gcd`:
`∀ (a b : ℕ), binaryGcd a b = Nat.gcd a b`
Structure the proof cleanly using auxiliary lemmas for parity, factor-of-two elimination, and subtraction invariants, reusing Mathlib where appropriate without verbatim copying.

### R3. Step Counting & Bound
Define companion step-counting or an instrumented representation that counts recursive transitions, establishing an explicit upper bound on step count in terms of bit length / logarithmic size.

### R4. Build & Verification Integrity
Ensure the repository compiles cleanly with `lake build` without unresolved `sorry`s in the final theorems.

### R5. Documentation
Provide clear markdown documentation explaining the architecture of the formalization, the DAG of invariant lemmas, and proof notes for future reuse/upstream contribution.

## Acceptance Criteria

### Verification
- [ ] Running `lake build` in `/home/deck/projects/amort` succeeds with 0 errors and 0 warnings.
- [ ] `#print axioms` on the main correctness theorem confirms it does not rely on `sorryAx`.
- [ ] Equivalence with `Nat.gcd` is proven for all `a, b : ℕ`.
- [ ] Step count definition and upper bound theorem are proven.
- [ ] Documentation file exists and describes the implementation and invariant lemma structure.
