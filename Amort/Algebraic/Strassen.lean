/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Mathlib.Algebra.Ring.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring

/-!
# Strassen's Sub-Cubic Matrix Multiplication

This module formalizes Volker Strassen's (1969) sub-cubic matrix multiplication algorithm:

1. **$2 \times 2$ Block Matrix Representation**:
   - `Matrix2x2 R` with blocks $A_{11}, A_{12}, A_{21}, A_{22}$ over an arbitrary ring $R$
     (including non-commutative rings of submatrices).
   - Standard block matrix addition, subtraction, and multiplication (8 sub-multiplications).

2. **Strassen's 7 Recursive Multiplications**:
   - $M_1 = (A_{11} + A_{22}) \cdot (B_{11} + B_{22})$
   - $M_2 = (A_{21} + A_{22}) \cdot B_{11}$
   - $M_3 = A_{11} \cdot (B_{12} - B_{22})$
   - $M_4 = A_{22} \cdot (B_{21} - B_{11})$
   - $M_5 = (A_{11} + A_{12}) \cdot B_{22}$
   - $M_6 = (A_{21} - A_{11}) \cdot (B_{11} + B_{12})$
   - $M_7 = (A_{12} - A_{22}) \cdot (B_{21} + B_{22})$

3. **Reconstruction & Algebraic Equivalence**:
   - $C_{11} = M_1 + M_4 - M_5 + M_7$
   - $C_{12} = M_3 + M_5$
   - $C_{21} = M_2 + M_4$
   - $C_{22} = M_1 - M_2 + M_3 + M_6$
   - Equivalence Theorem: Strassen's 7-multiplication product exactly equals standard product
     in any ring $R$.

4. **Divide-and-Conquer Recurrence & Sub-Cubic Bound**:
   - Recurrence relation $T(n) \le 7T(n/2) + c \cdot n^2$.
   - Dyadic closed form bound $T(2^k) \le (T(1) + 2c) \cdot 7^k$.
   - Operational work model `strassenWork n = 7 ^ (Nat.size n)`.
   - Sub-cubic exponent: $\log_2 7 < 3$, yielding $O(n^{\log_2 7}) \approx O(n^{2.807})$.

## Key Definitions and Theorems
- `Amort.Algebraic.Matrix2x2`: $2 \times 2$ block matrix structure.
- `Amort.Algebraic.Matrix2x2.mul`: Standard matrix product (8 multiplications).
- `Amort.Algebraic.Matrix2x2.strassenMul`: Strassen product (7 multiplications).
- `Amort.Algebraic.Matrix2x2.strassen_mul_eq_std_mul`: Algebraic equivalence theorem.
- `Amort.Algebraic.StrassenRecurrence`: Recurrence $T(n) \le 7T(n/2) + c \cdot n^2$.
- `Amort.Algebraic.strassen_dyadic_bound`: Bound $T(2^k) \le (T(1) + 2c) \cdot 7^k$.
- `Amort.Algebraic.strassen_subcubic_exponent`: Rigorous proof that $\log_2 7 < 3$.
-/

namespace Amort.Algebraic

/-! ### $2 \times 2$ Block Matrix Structure and Standard Operations -/

/-- A $2 \times 2$ block matrix with entries from an arbitrary (possibly non-commutative)
ring $R$. -/
structure Matrix2x2 (R : Type*) where
  a11 : R
  a12 : R
  a21 : R
  a22 : R

namespace Matrix2x2

variable {R : Type*} [Ring R]

/-- Matrix addition for $2 \times 2$ block matrices. -/
def add (A B : Matrix2x2 R) : Matrix2x2 R :=
  ⟨A.a11 + B.a11, A.a12 + B.a12, A.a21 + B.a21, A.a22 + B.a22⟩

/-- Matrix subtraction for $2 \times 2$ block matrices. -/
def sub (A B : Matrix2x2 R) : Matrix2x2 R :=
  ⟨A.a11 - B.a11, A.a12 - B.a12, A.a21 - B.a21, A.a22 - B.a22⟩

/-- Standard block matrix multiplication performing 8 recursive sub-multiplications. -/
def mul (A B : Matrix2x2 R) : Matrix2x2 R :=
  ⟨A.a11 * B.a11 + A.a12 * B.a21,
   A.a11 * B.a12 + A.a12 * B.a22,
   A.a21 * B.a11 + A.a22 * B.a21,
   A.a21 * B.a12 + A.a22 * B.a22⟩

/-! ### Strassen's 7 Multiplications -/

/-- Strassen auxiliary multiplication $M_1 = (A_{11} + A_{22}) \cdot (B_{11} + B_{22})$. -/
def M1 (A B : Matrix2x2 R) : R :=
  (A.a11 + A.a22) * (B.a11 + B.a22)

/-- Strassen auxiliary multiplication $M_2 = (A_{21} + A_{22}) \cdot B_{11}$. -/
def M2 (A B : Matrix2x2 R) : R :=
  (A.a21 + A.a22) * B.a11

/-- Strassen auxiliary multiplication $M_3 = A_{11} \cdot (B_{12} - B_{22})$. -/
def M3 (A B : Matrix2x2 R) : R :=
  A.a11 * (B.a12 - B.a22)

/-- Strassen auxiliary multiplication $M_4 = A_{22} \cdot (B_{21} - B_{11})$. -/
def M4 (A B : Matrix2x2 R) : R :=
  A.a22 * (B.a21 - B.a11)

/-- Strassen auxiliary multiplication $M_5 = (A_{11} + A_{12}) \cdot B_{22}$. -/
def M5 (A B : Matrix2x2 R) : R :=
  (A.a11 + A.a12) * B.a22

/-- Strassen auxiliary multiplication $M_6 = (A_{21} - A_{11}) \cdot (B_{11} + B_{12})$. -/
def M6 (A B : Matrix2x2 R) : R :=
  (A.a21 - A.a11) * (B.a11 + B.a12)

/-- Strassen auxiliary multiplication $M_7 = (A_{12} - A_{22}) \cdot (B_{21} + B_{22})$. -/
def M7 (A B : Matrix2x2 R) : R :=
  (A.a12 - A.a22) * (B.a21 + B.a22)

/-! ### Strassen Block Reconstruction -/

/-- Top-left block: $C_{11} = M_1 + M_4 - M_5 + M_7$. -/
def strassenC11 (A B : Matrix2x2 R) : R :=
  M1 A B + M4 A B - M5 A B + M7 A B

/-- Top-right block: $C_{12} = M_3 + M_5$. -/
def strassenC12 (A B : Matrix2x2 R) : R :=
  M3 A B + M5 A B

/-- Bottom-left block: $C_{21} = M_2 + M_4$. -/
def strassenC21 (A B : Matrix2x2 R) : R :=
  M2 A B + M4 A B

/-- Bottom-right block: $C_{22} = M_1 - M_2 + M_3 + M_6$. -/
def strassenC22 (A B : Matrix2x2 R) : R :=
  M1 A B - M2 A B + M3 A B + M6 A B

/-- Complete Strassen matrix product reconstructed from the 7 products $M_1, \dots, M_7$. -/
def strassenMul (A B : Matrix2x2 R) : Matrix2x2 R :=
  ⟨strassenC11 A B, strassenC12 A B, strassenC21 A B, strassenC22 A B⟩

/-! ### Algebraic Equivalence Theorems -/

/-- Algebraic equivalence for block (1, 1): $M_1 + M_4 - M_5 + M_7 = A_{11} B_{11} + A_{12} B_{21}$
holds in any ring $R$. -/
theorem strassen_c11_eq (A B : Matrix2x2 R) :
    strassenC11 A B = A.a11 * B.a11 + A.a12 * B.a21 := by
  unfold strassenC11 M1 M4 M5 M7
  noncomm_ring

/-- Algebraic equivalence for block (1, 2): $M_3 + M_5 = A_{11} B_{12} + A_{12} B_{22}$
holds in any ring $R$. -/
theorem strassen_c12_eq (A B : Matrix2x2 R) :
    strassenC12 A B = A.a11 * B.a12 + A.a12 * B.a22 := by
  unfold strassenC12 M3 M5
  noncomm_ring

/-- Algebraic equivalence for block (2, 1): $M_2 + M_4 = A_{21} B_{11} + A_{22} B_{21}$
holds in any ring $R$. -/
theorem strassen_c21_eq (A B : Matrix2x2 R) :
    strassenC21 A B = A.a21 * B.a11 + A.a22 * B.a21 := by
  unfold strassenC21 M2 M4
  noncomm_ring

/-- Algebraic equivalence for block (2, 2): $M_1 - M_2 + M_3 + M_6 = A_{21} B_{12} + A_{22} B_{22}$
holds in any ring $R$. -/
theorem strassen_c22_eq (A B : Matrix2x2 R) :
    strassenC22 A B = A.a21 * B.a12 + A.a22 * B.a22 := by
  unfold strassenC22 M1 M2 M3 M6
  noncomm_ring

/-- Strassen's matrix multiplication using 7 recursive products is mathematically equivalent
to the standard matrix product in any ring $R$. -/
theorem strassen_mul_eq_std_mul (A B : Matrix2x2 R) :
    strassenMul A B = mul A B := by
  unfold strassenMul mul
  congr 1
  · exact strassen_c11_eq A B
  · exact strassen_c12_eq A B
  · exact strassen_c21_eq A B
  · exact strassen_c22_eq A B

end Matrix2x2

/-! ### Recurrence Relations and Sub-Cubic Complexity -/

/-- Standard cubic matrix multiplication operational work model: $2 n^3$. -/
def standardMatrixMulWork (n : ℕ) : ℕ :=
  2 * n ^ 3

/-- Standard matrix multiplication has cubic complexity $2 n^3$. -/
theorem standardMatrixMulWork_cubic (n : ℕ) :
    standardMatrixMulWork n = 2 * n ^ 3 :=
  rfl

/-- Strassen's divide-and-conquer recurrence:
$T(n) \le 7 T(n / 2) + c \cdot n^2$ for all $n \ge 2$. -/
def StrassenRecurrence (T : ℕ → ℕ) (c : ℕ) : Prop :=
  ∀ n ≥ 2, T n ≤ 7 * T (n / 2) + c * n ^ 2

/-- Helper geometric sum for Strassen's recurrence:
$\sum_{j=0}^{k-1} 7^{k-1-j} 4^j = \frac{7^k - 4^k}{3}$. -/
def geomSum74 : ℕ → ℕ
  | 0 => 0
  | k + 1 => 7 * geomSum74 k + 4 ^ k

/-- Closed-form identity: $3 \cdot \text{geomSum74 } k = 7^k - 4^k$. -/
theorem geomSum74_eq (k : ℕ) : 3 * geomSum74 k = 7 ^ k - 4 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    unfold geomSum74
    have h4le7 : 4 ^ k ≤ 7 ^ k := Nat.pow_le_pow_left (by decide) k
    have h4le7' : 4 ^ (k + 1) ≤ 7 ^ (k + 1) := Nat.pow_le_pow_left (by decide) (k + 1)
    have h7 : 7 ^ (k + 1) = 7 ^ k * 7 := by rw [pow_succ]
    have h4 : 4 ^ (k + 1) = 4 ^ k * 4 := by rw [pow_succ]
    omega

/-- Geometric sum upper bound: $\text{geomSum74 } k \le 7^k$. -/
theorem geomSum74_le_pow7 (k : ℕ) : geomSum74 k ≤ 7 ^ k := by
  have h := geomSum74_eq k
  have hle : 7 ^ k - 4 ^ k ≤ 7 ^ k := Nat.sub_le _ _
  omega

/-- Exact dyadic recurrence bound: For any function $T$ satisfying Strassen's recurrence,
$T(2^k) \le 7^k T(1) + 4c \cdot \text{geomSum74 } k$. -/
theorem strassen_dyadic_exact (T : ℕ → ℕ) (c : ℕ) (hrec : StrassenRecurrence T c) (k : ℕ) :
    T (2 ^ k) ≤ 7 ^ k * T 1 + 4 * c * geomSum74 k := by
  induction k with
  | zero =>
    unfold geomSum74
    simp
  | succ k ih =>
    have h2le : 2 ≤ 2 ^ (k + 1) := by
      have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      omega
    have hstep := hrec (2 ^ (k + 1)) h2le
    have hdiv : 2 ^ (k + 1) / 2 = 2 ^ k := by
      have : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ, mul_comm]
      rw [this]
      exact Nat.mul_div_cancel_left (2 ^ k) zero_lt_two
    rw [hdiv] at hstep
    have hsq : (2 ^ (k + 1)) ^ 2 = 4 * 4 ^ k := by
      have h1 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ, mul_comm]
      rw [h1, mul_pow]
      have h2 : (2 ^ k) ^ 2 = 4 ^ k := by
        rw [← pow_mul, mul_comm k 2, pow_mul]
        rfl
      rw [h2]
      ring
    rw [hsq] at hstep
    unfold geomSum74
    have h7_pow : 7 ^ (k + 1) = 7 * 7 ^ k := by rw [pow_succ, mul_comm]
    calc T (2 ^ (k + 1))
      _ ≤ 7 * T (2 ^ k) + c * (4 * 4 ^ k) := hstep
      _ ≤ 7 * (7 ^ k * T 1 + 4 * c * geomSum74 k) + c * (4 * 4 ^ k) := by omega
      _ = (7 * 7 ^ k) * T 1 + 4 * c * (7 * geomSum74 k + 4 ^ k) := by ring
      _ = 7 ^ (k + 1) * T 1 + 4 * c * (7 * geomSum74 k + 4 ^ k) := by rw [h7_pow]

/-- Dyadic power bound: For any function $T$ satisfying Strassen's recurrence,
$T(2^k) \le (T(1) + 2c) \cdot 7^k$. -/
theorem strassen_dyadic_bound (T : ℕ → ℕ) (c : ℕ) (hrec : StrassenRecurrence T c) (k : ℕ) :
    T (2 ^ k) ≤ (T 1 + 2 * c) * 7 ^ k := by
  have hexact := strassen_dyadic_exact T c hrec k
  have hgeom := geomSum74_eq k
  have h4le7 : 4 ^ k ≤ 7 ^ k := Nat.pow_le_pow_left (by decide) k
  have h_bound : 3 * (4 * c * geomSum74 k) ≤ 3 * (2 * c * 7 ^ k) := by
    calc 3 * (4 * c * geomSum74 k)
      _ = 4 * c * (3 * geomSum74 k) := by ring
      _ = 4 * c * (7 ^ k - 4 ^ k) := by rw [hgeom]
      _ ≤ 4 * c * 7 ^ k := by
        have : 7 ^ k - 4 ^ k ≤ 7 ^ k := Nat.sub_le (7 ^ k) (4 ^ k)
        exact Nat.mul_le_mul_left (4 * c) this
      _ ≤ 6 * c * 7 ^ k := by
        have : 4 * c ≤ 6 * c := by omega
        exact Nat.mul_le_mul_right (7 ^ k) this
      _ = 3 * (2 * c * 7 ^ k) := by ring
  have h_div3 : 4 * c * geomSum74 k ≤ 2 * c * 7 ^ k := by omega
  calc T (2 ^ k)
    _ ≤ 7 ^ k * T 1 + 4 * c * geomSum74 k := hexact
    _ ≤ 7 ^ k * T 1 + 2 * c * 7 ^ k := by omega
    _ = (T 1 + 2 * c) * 7 ^ k := by ring

/-- Concrete operational work model for Strassen's algorithm:
$W(n) = 7^{\text{Nat.size } n}$. -/
def strassenWork (n : ℕ) : ℕ :=
  7 ^ (Nat.size n)

/-- Operational work is bounded by $7^{\text{Nat.size } n}$. -/
theorem strassenWork_le (n : ℕ) (_hn : 1 ≤ n) :
    strassenWork n ≤ 7 ^ (Nat.size n) :=
  le_rfl

/-- Operational work bounded by $7^{k+1}$ when $n \le 2^k$. -/
theorem strassenWork_le_pow7 (n k : ℕ) (_hn : 1 ≤ n) (hle : n ≤ 2 ^ k) :
    strassenWork n ≤ 7 ^ (k + 1) := by
  unfold strassenWork
  have hsize_le : Nat.size n ≤ k + 1 := by
    rw [Nat.size_le]
    calc n ≤ 2 ^ k := hle
      _ < 2 ^ (k + 1) := by
        have : 0 < 2 ^ k := Nat.two_pow_pos k
        omega
  exact Nat.pow_le_pow_right (by decide) hsize_le

/-- Strict sub-cubic exponent theorem:
The Strassen complexity exponent $\log_2 7 = \frac{\ln 7}{\ln 2}$ is strictly less than 3,
rigorously proving that Strassen's algorithm is sub-cubic:
$$\log_2 7 < 3$$ -/
theorem strassen_subcubic_exponent : Real.log 7 / Real.log 2 < 3 := by
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have h7pos : (0 : ℝ) < 7 := by norm_num
  have h2lt : 1 < (2 : ℝ) := by norm_num
  have hlog2pos : 0 < Real.log 2 := Real.log_pos h2lt
  rw [div_lt_iff₀ hlog2pos]
  have h78 : (7 : ℝ) < 8 := by norm_num
  have hlog : Real.log 7 < Real.log 8 := Real.log_lt_log h7pos h78
  have h8 : (8 : ℝ) = 2 ^ 3 := by norm_num
  rw [h8, Real.log_pow] at hlog
  push_cast at hlog
  linarith

end Amort.Algebraic
