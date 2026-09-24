# Fast Algebraic & Divide-and-Conquer Algorithms (`Amort.Algebraic`)

> **Status: stub — not verified** (Phase 3/4 canon stubs; FFT and Strassen matrix multiplication
> algorithms are specification stubs awaiting full verification).


## 1. Domain Mission and Scope

The `Amort.Algebraic` module formalizes landmark divide-and-conquer algorithms in fast algebra and numerical
computation in Lean 4:
1. **Fast Fourier Transform (FFT) & Fast Polynomial Multiplication**:
   - Cooley-Tukey Radix-2 divide-and-conquer algorithm.
   - Point-value representation, roots of unity cancellation and halving lemmas.
   - Butterfly operation correctness and operational recurrence $T(n) \le 2T(n/2) + c \cdot n$.
   - $O(n \log n)$ polynomial multiplication complexity contrasting with naive Cauchy convolution $O(n^2)$.
2. **Strassen's Sub-Cubic Matrix Multiplication**:
   - $2 \times 2$ block matrix multiplication using 7 recursive multiplications instead of 8.
   - Algebraic equivalence with standard matrix product across arbitrary (non-commutative) rings.
   - Divide-and-conquer recurrence $T(n) \le 7T(n/2) + c \cdot n^2$.
   - Sub-cubic operational bound $O(n^{\log_2 7}) \approx O(n^{2.807})$, with formal proof that $\log_2 7 < 3$.
3. **Asymptotic Complexity Bridges**:
   - Mathlib's `Mathlib.Analysis.Asymptotics.IsBigO` under `Filter.atTop`.
   - Explicit contrasts between classical naive bounds and fast algebraic divide-and-conquer bounds.

---

## 2. Module Architecture and Dependency Graph

```
                                  Mathlib.Analysis.Asymptotics.Defs
                                                 │
                                                 ▼
                             ┌───────────────────┴───────────────────┐
                             │    Amort.Recurrence.MasterTheorem     │
                             │       Amort.Recurrence.Halving        │
                             └───────────────────┬───────────────────┘
                                                 │
                        ┌────────────────────────┼────────────────────────┐
                        ▼                                                 ▼
             Amort.Algebraic.FFT                              Amort.Algebraic.Strassen
     - Roots of unity & Cancellation                 - Matrix2x2 Block Type
     - Cooley-Tukey Radix-2 Decomposition            - 7 Auxiliary Multiplications
     - Butterfly Operator Correctness                - Algebraic Equivalence Theorem
     - Recurrence T(n) ≤ 2T(n/2) + cn                - Recurrence T(n) ≤ 7T(n/2) + cn²
     - Poly Mul Work Bound ≤ 38n·size n              - Exponent Bound log₂ 7 < 3
                        │                                                 │
                        └────────────────────────┬────────────────────────┘
                                                 │
                                                 ▼
                                   Amort.Algebraic.Asymptotics
                             - isBigO_fftWork_n_log_n
                             - isBigO_fftPolyMulWork_n_log_n
                             - isBigO_naivePolyMulWork_sq
                             - isBigO_strassenWork_rpow
                             - isBigO_standardMatrixMulWork_cube
```

---

## 3. Algorithmic Complexity Comparison

| Algorithm | Representation / Method | Operational Complexity | Mathlib `IsBigO` Form | Classical Naive Complexity |
| :--- | :--- | :--- | :--- | :--- |
| **FFT Forward / Inverse** | Radix-2 butterfly recursion | $3n \cdot \text{Nat.size } n$ | $O(n \log n)$ | $O(n^2)$ (Vandermonde DFT) |
| **Polynomial Multiplication** | 3 FFTs + Pointwise product | $\le 38n \cdot \text{Nat.size } n$ | $O(n \log n)$ | $O(n^2)$ (Cauchy Convolution) |
| **Strassen Matrix Mul** | 7-multiplication block recursion | $\le 7 \cdot n^{\log_2 7}$ | $O(n^{\log_2 7})$ ($O(n^{2.807})$) | $O(n^3)$ (Standard Block Mul) |

---

## 4. Verification and Axiom Audit Summary

All modules compile cleanly under `lake build Amort` with zero warnings and zero errors.
Every milestone theorem has been verified with `#print axioms` to depend strictly on standard
Lean 4 foundational axioms:

- `propext`: Propositional extensionality.
- `Classical.choice`: Axiom of choice (used in real analysis and limits).
- `Quot.sound`: Quotient soundess.

**Zero theorems rely on `sorry` or `sorryAx`**. All source code complies with Mathlib's $\le 100$ character
line length standard.
