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

## 2026-09-07T21:01:05Z

Connect Binary GCD complexity bounds to Mathlib's `Asymptotics.IsBigO`, formalize step counting for standard Euclidean GCD with a logarithmic upper bound, and conduct a dedicated style guide audit for full Mathlib readiness.

Working directory: /home/deck/projects/amort
Integrity mode: demo

## Requirements

### R1. Formalize Standard Euclidean GCD Step Counting & Upper Bound
Define the step counter `euclideanGcdSteps (a b : ℕ) : ℕ` mirroring `Nat.gcd a b`. Prove provable termination and establish an upper bound showing `euclideanGcdSteps a b ≤ 2 * Nat.size (min a b) + 1` (or in terms of `size (a + b)`), formalizing the halving property of modulo ($a \bmod b < a / 2$ when $b \le a$).

### R2. Asymptotics Bridge to Mathlib `IsBigO`
Connect the proven step bounds for Binary GCD to Mathlib's `Asymptotics.IsBigO` under the `atTop` filter on the combined input measure (or size of $a + b$ / $\min(a, b)$), providing idiomatic asymptotic complexity theorems.

### R3. Style Guide & Linter Audit
Ensure all new and updated code strictly adheres to Mathlib conventions:
- Scoped under `namespace Nat` (or appropriate sub-namespace).
- Uses `lemma` for auxiliaries and `theorem` for milestones.
- Docstrings formatted as `/-- ... -/` without assignment metadata tags.
- Line length ≤ 100 characters.
- Zero `sorryAx` or non-standard axioms verified via `#print axioms`.

### R4. Build & Documentation
The repository must build cleanly with `lake build` (0 warnings, 0 errors). Provide clear documentation explaining the module structure, theorem statements, and asymptotic definitions.

## Acceptance Criteria

### Verification
- [ ] Running `lake build` in `/home/deck/projects/amort` succeeds with 0 errors and 0 warnings.
- [ ] `#print axioms` on the main asymptotic and Euclidean step bound theorems confirms zero `sorryAx`.
- [ ] `euclideanGcdSteps` is defined, terminates, and its logarithmic upper bound is formally proven.
- [ ] `IsBigO` connection theorem is proven using Mathlib's asymptotics library.
- [ ] Code passes style check guidelines (proper namespacing, docstrings, line lengths).
- [ ] Documentation file exists and describes the new formalizations.
