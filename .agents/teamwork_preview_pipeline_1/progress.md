# Progress: Binary GCD Formalization in Lean 4

## Status: COMPLETE

### Requirements Checklist
- [x] R1. Formal Definition and Termination:
  - `binaryGcd` defined in `Amort/BinaryGCD.lean` with termination by `a + b` discharged via `omega`.
- [x] R2. Mathematical Equivalence with Nat.gcd:
  - Proven in `binaryGcd_eq_gcd : ∀ a b, binaryGcd a b = Nat.gcd a b` with complete invariant lemma DAG.
- [x] R3. Step Counting & Bound:
  - Companion `binaryGcdSteps` and instrumented `binaryGcdWithSteps` defined.
  - Equivalence theorems `binaryGcdWithSteps_fst`, `binaryGcdWithSteps_snd`, `binaryGcdWithSteps_eq_gcd` proven.
  - Upper bounds `binaryGcdSteps_le_size_add_size` and `binaryGcdSteps_le_two_mul_size_add` proven.
- [x] R4. Build & Verification Integrity:
  - `lake build` completes cleanly with 0 errors and 0 warnings.
  - `#print axioms` confirms no reliance on `sorryAx`.
- [x] R5. Documentation:
  - Comprehensive documentation created in `docs/BinaryGCD.md`.
  - Project `README.md` updated.

### Acceptance Criteria Verification
- [x] Running `lake build` in `/home/deck/projects/amort` succeeds with 0 errors and 0 warnings.
- [x] `#print axioms` on the main correctness theorem confirms it does not rely on `sorryAx`.
- [x] Equivalence with `Nat.gcd` is proven for all `a, b : ℕ`.
- [x] Step count definition and upper bound theorem are proven.
- [x] Documentation file exists and describes the implementation and invariant lemma structure.
- [x] Tracking files (`progress.md`, `plan.md`, `BRIEFING.md`) maintained in working directory.
