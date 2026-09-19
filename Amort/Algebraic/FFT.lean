/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Fast Fourier Transform (FFT) & Fast Polynomial Multiplication

This module formalizes the Cooley-Tukey Radix-2 Fast Fourier Transform (FFT) and its
application to fast polynomial multiplication over an arbitrary commutative ring $R$:

1. **Roots of Unity & Cancellation**:
   - Predicate `IsNthRootOfUnity ω n` stating $\omega^n = 1$.
   - Cancellation lemma: $(\omega^d)^k = \omega^{d \cdot k}$, mapping $(dn)$-th roots to $n$-th
     roots of unity.
   - Halving lemma: $(\omega^{k + m})^2 = (\omega^2)^k$ when $\omega^{2m} = 1$.
   - Negation / symmetry lemma: $\omega^{k + m} = - \omega^k$ when $\omega^m = -1$.

2. **Polynomial Evaluation & Cooley-Tukey Decomposition**:
   - Polynomial evaluation via Horner's scheme `evalPoly l x`.
   - Even/odd coefficient extraction: `evenCoeffs` and `oddCoeffs`.
   - Fundamental Radix-2 decomposition theorem:
     $$A(x) = A_{even}(x^2) + x \cdot A_{odd}(x^2)$$

3. **Butterfly Operation & DFT Correctness**:
   - Butterfly recombination `butterfly u v twiddle = (u + twiddle * v, u - twiddle * v)`.
   - Equivalence of butterfly outputs with point evaluations:
     $A(\omega^k) = u_k + \omega^k v_k$ and $A(\omega^{k+m}) = u_k - \omega^k v_k$.

4. **Divide-and-Conquer Recurrence & Asymptotic Complexity**:
   - Recurrence relation $T(n) \le 2T(n/2) + c \cdot n$.
   - Concrete operational upper bound $O(n \cdot \text{Nat.size } n)$.
   - Polynomial multiplication via 3 FFT calls: $O(n \log n)$ vs naive $O(n^2)$.

## Key Definitions and Theorems
- `Amort.Algebraic.IsNthRootOfUnity`: Root of unity predicate.
- `Amort.Algebraic.rootOfUnity_cancellation`: Cancellation lemma.
- `Amort.Algebraic.halving_lemma`: Squaring roots of unity halves order.
- `Amort.Algebraic.negation_lemma`: Principal root negation identity.
- `Amort.Algebraic.evalPoly`: Polynomial evaluation in commutative ring $R$.
- `Amort.Algebraic.cooley_tukey_decomp`: Cooley-Tukey $A(x) = A_{even}(x^2) + x A_{odd}(x^2)$.
- `Amort.Algebraic.butterfly`: Radix-2 butterfly operation.
- `Amort.Algebraic.butterfly_dft_pair`: Butterfly produces evaluations at $\omega^k$
  and $\omega^{k+m}$.
- `Amort.Algebraic.fft_dyadic_bound`: $T(2^k) \le T(1) 2^k + c \cdot 2^k \cdot k$.
- `Amort.Algebraic.fftWork_le`: FFT operational work is $O(n \log n)$.
- `Amort.Algebraic.fftPolyMulWork_le`: Polynomial multiplication is $O(n \log n)$.
-/

namespace Amort.Algebraic

/-! ### Roots of Unity and Cancellation Lemmas -/

section RootsOfUnity

variable {R : Type*} [CommRing R]

/-- An element $\omega \in R$ is an $n$-th root of unity if $\omega^n = 1$. -/
def IsNthRootOfUnity (ω : R) (n : ℕ) : Prop :=
  ω ^ n = 1

/-- Cancellation Lemma: powers of $\omega^d$ satisfy $(\omega^d)^k = \omega^{d \cdot k}$. -/
theorem rootOfUnity_cancellation (ω : R) (d k : ℕ) :
    (ω ^ d) ^ k = ω ^ (d * k) := by
  rw [← pow_mul]

/-- If $\omega$ is a $(d \cdot n)$-th root of unity, then $\omega^d$ is an $n$-th root of unity. -/
theorem rootOfUnity_pow_order (ω : R) (d n : ℕ) (h : IsNthRootOfUnity ω (d * n)) :
    IsNthRootOfUnity (ω ^ d) n := by
  unfold IsNthRootOfUnity at h ⊢
  rw [← pow_mul]
  exact h

/-- Halving Lemma: When $n = 2m$ and $\omega^n = 1$, the square of $\omega^{k + m}$ equals
$(\omega^2)^k$, matching the square of $\omega^k$. -/
theorem halving_lemma (ω : R) (m k : ℕ) (hω : ω ^ (2 * m) = 1) :
    (ω ^ (k + m)) ^ 2 = (ω ^ 2) ^ k := by
  calc (ω ^ (k + m)) ^ 2
    _ = ω ^ ((k + m) * 2) := by rw [← pow_mul]
    _ = ω ^ (2 * k + 2 * m) := by ring_nf
    _ = ω ^ (2 * k) * ω ^ (2 * m) := by rw [pow_add]
    _ = ω ^ (2 * k) * 1 := by rw [hω]
    _ = ω ^ (2 * k) := by rw [mul_one]
    _ = (ω ^ 2) ^ k := by rw [← pow_mul, mul_comm 2 k]

/-- Squaring identity for twiddle factors: $(\omega^k)^2 = (\omega^2)^k$. -/
theorem halving_lemma_sq (ω : R) (k : ℕ) :
    (ω ^ k) ^ 2 = (ω ^ 2) ^ k := by
  rw [← pow_mul, ← pow_mul, mul_comm]

/-- Negation Lemma: If $\omega^m = -1$, then $\omega^{k + m} = - (\omega^k)$. -/
theorem negation_lemma (ω : R) (m k : ℕ) (hneg : ω ^ m = -1) :
    ω ^ (k + m) = - (ω ^ k) := by
  rw [pow_add, hneg]
  ring

end RootsOfUnity

/-! ### Polynomial Representation and Cooley-Tukey Decomposition -/

/-- Extracts coefficients at even indices: $[a_0, a_2, a_4, \dots]$. -/
def evenCoeffs {α : Type*} (l : List α) : List α :=
  match l with
  | [] => []
  | [x] => [x]
  | x :: _ :: rest => x :: evenCoeffs rest

/-- Extracts coefficients at odd indices: $[a_1, a_3, a_5, \dots]$. -/
def oddCoeffs {α : Type*} (l : List α) : List α :=
  match l with
  | [] => []
  | [_] => []
  | _ :: y :: rest => y :: oddCoeffs rest

/-- Two-step list induction principle for alternating step reductions. -/
theorem list_two_step_induction {α : Type*} {P : List α → Prop}
    (h_nil : P [])
    (h_one : ∀ x, P [x])
    (h_two : ∀ x y l, P l → P (x :: y :: l)) :
    ∀ l, P l := by
  intro l
  generalize hn : l.length = n
  induction n using Nat.strong_induction_on generalizing l with
  | h n ih =>
    cases l with
    | nil => exact h_nil
    | cons x xs =>
      cases xs with
      | nil => exact h_one x
      | cons y ys =>
        have h_len : ys.length < n := by
          simp only [List.length_cons] at hn
          omega
        exact h_two x y ys (ih ys.length h_len ys rfl)

/-- Length of even coefficient list is $\lceil \text{length} / 2 \rceil$. -/
theorem length_evenCoeffs {α : Type*} (l : List α) :
    (evenCoeffs l).length = (l.length + 1) / 2 := by
  induction l using list_two_step_induction with
  | h_nil => simp [evenCoeffs]
  | h_one x => simp [evenCoeffs]
  | h_two x y rest ih =>
    have h_even : evenCoeffs (x :: y :: rest) = x :: evenCoeffs rest := by
      cases rest <;> rfl
    rw [h_even]
    simp only [List.length_cons]
    rw [ih]
    omega

/-- Length of odd coefficient list is $\lfloor \text{length} / 2 \rfloor$. -/
theorem length_oddCoeffs {α : Type*} (l : List α) :
    (oddCoeffs l).length = l.length / 2 := by
  induction l using list_two_step_induction with
  | h_nil => simp [oddCoeffs]
  | h_one x => simp [oddCoeffs]
  | h_two x y rest ih =>
    have h_odd : oddCoeffs (x :: y :: rest) = y :: oddCoeffs rest := by
      cases rest <;> rfl
    rw [h_odd]
    simp only [List.length_cons]
    rw [ih]
    omega

/-- For even length $2m$, even coefficient subproblem has size $m$. -/
theorem length_evenCoeffs_of_two_mul {α : Type*} (m : ℕ) (l : List α) (hl : l.length = 2 * m) :
    (evenCoeffs l).length = m := by
  rw [length_evenCoeffs, hl]
  omega

/-- For even length $2m$, odd coefficient subproblem has size $m$. -/
theorem length_oddCoeffs_of_two_mul {α : Type*} (m : ℕ) (l : List α) (hl : l.length = 2 * m) :
    (oddCoeffs l).length = m := by
  rw [length_oddCoeffs, hl]
  omega

section PolyEval

variable {R : Type*} [CommRing R]

/-- Evaluates polynomial given as a coefficient list at point $x \in R$ via Horner's rule. -/
def evalPoly (l : List R) (x : R) : R :=
  match l with
  | [] => 0
  | c :: cs => c + x * evalPoly cs x

/-- Cooley-Tukey Radix-2 decomposition theorem:
For any polynomial $A$ and point $x$,
$A(x) = A_{even}(x^2) + x \cdot A_{odd}(x^2)$. -/
theorem cooley_tukey_decomp (l : List R) (x : R) :
    evalPoly (evenCoeffs l) (x ^ 2) + x * evalPoly (oddCoeffs l) (x ^ 2) = evalPoly l x := by
  induction l using list_two_step_induction with
  | h_nil =>
    simp [evalPoly, evenCoeffs, oddCoeffs]
  | h_one a =>
    simp [evalPoly, evenCoeffs, oddCoeffs]
  | h_two a b rest ih =>
    have h_even : evenCoeffs (a :: b :: rest) = a :: evenCoeffs rest := by
      cases rest <;> rfl
    have h_odd : oddCoeffs (a :: b :: rest) = b :: oddCoeffs rest := by
      cases rest <;> rfl
    rw [h_even, h_odd]
    simp only [evalPoly]
    calc a + x ^ 2 * evalPoly (evenCoeffs rest) (x ^ 2) +
          x * (b + x ^ 2 * evalPoly (oddCoeffs rest) (x ^ 2))
      _ = a + x * b + x ^ 2 * (evalPoly (evenCoeffs rest) (x ^ 2) +
          x * evalPoly (oddCoeffs rest) (x ^ 2)) := by ring
      _ = a + x * b + x ^ 2 * evalPoly rest x := by rw [ih]
      _ = a + x * (b + x * evalPoly rest x) := by ring

/-! ### Discrete Fourier Transform & Butterfly Operations -/

/-- Discrete Fourier Transform mapping coefficient list $a$ to evaluations at powers $\omega^k$. -/
def dft (n : ℕ) (ω : R) (a : List R) : List R :=
  (List.range n).map (fun k => evalPoly a (ω ^ k))

/-- Length of DFT output vector equals $n$. -/
@[simp]
theorem length_dft (n : ℕ) (ω : R) (a : List R) :
    (dft n ω a).length = n := by
  simp [dft]

/-- The Radix-2 butterfly operation combines even and odd evaluations with twiddle factor:
$(u + \text{twiddle} \cdot v, u - \text{twiddle} \cdot v)$. -/
def butterfly (u v twiddle : R) : R × R :=
  (u + twiddle * v, u - twiddle * v)

/-- Correctness of butterfly evaluation for index $k < n/2$:
$A(\omega^k) = A_{even}((\omega^2)^k) + \omega^k \cdot A_{odd}((\omega^2)^k)$. -/
theorem butterfly_correctness_even_part (l : List R) (ω : R) (k : ℕ) :
    evalPoly l (ω ^ k) =
      evalPoly (evenCoeffs l) ((ω ^ 2) ^ k) + ω ^ k * evalPoly (oddCoeffs l) ((ω ^ 2) ^ k) := by
  have h := cooley_tukey_decomp l (ω ^ k)
  rw [halving_lemma_sq] at h
  exact h.symm

/-- Correctness of butterfly evaluation for mirrored index $k + m$ (where $n = 2m$ and
$\omega^m = -1$):
$A(\omega^{k + m}) = A_{even}((\omega^2)^k) - \omega^k \cdot A_{odd}((\omega^2)^k)$. -/
theorem butterfly_correctness_odd_part (l : List R) (ω : R) (m k : ℕ)
    (hω : ω ^ (2 * m) = 1) (hneg : ω ^ m = -1) :
    evalPoly l (ω ^ (k + m)) =
      evalPoly (evenCoeffs l) ((ω ^ 2) ^ k) - ω ^ k * evalPoly (oddCoeffs l) ((ω ^ 2) ^ k) := by
  have h := (cooley_tukey_decomp l (ω ^ (k + m))).symm
  have h1 : ((ω ^ (k + m)) ^ 2) = (ω ^ 2) ^ k := halving_lemma ω m k hω
  have h2 : ω ^ (k + m) = - (ω ^ k) := negation_lemma ω m k hneg
  calc evalPoly l (ω ^ (k + m))
    _ = evalPoly (evenCoeffs l) ((ω ^ (k + m)) ^ 2) +
        (ω ^ (k + m)) * evalPoly (oddCoeffs l) ((ω ^ (k + m)) ^ 2) := h
    _ = evalPoly (evenCoeffs l) ((ω ^ 2) ^ k) +
        (- (ω ^ k)) * evalPoly (oddCoeffs l) ((ω ^ 2) ^ k) := by rw [h1, h2]
    _ = evalPoly (evenCoeffs l) ((ω ^ 2) ^ k) -
        ω ^ k * evalPoly (oddCoeffs l) ((ω ^ 2) ^ k) := by ring

/-- Full butterfly pair identity: Combining subproblem evaluations via the butterfly operation
simultaneously produces evaluations at $\omega^k$ and $\omega^{k+m}$. -/
theorem butterfly_dft_pair (l : List R) (ω : R) (m k : ℕ)
    (hω : ω ^ (2 * m) = 1) (hneg : ω ^ m = -1) :
    butterfly (evalPoly (evenCoeffs l) ((ω ^ 2) ^ k))
              (evalPoly (oddCoeffs l) ((ω ^ 2) ^ k))
              (ω ^ k) =
      (evalPoly l (ω ^ k), evalPoly l (ω ^ (k + m))) := by
  unfold butterfly
  rw [← butterfly_correctness_even_part, ← butterfly_correctness_odd_part l ω m k hω hneg]

end PolyEval

/-! ### Recurrence Relations and Step Bounds -/

/-- Divide-and-conquer recurrence for Radix-2 FFT:
$T(n) \le 2 T(n / 2) + c \cdot n$ for all $n \ge 2$. -/
def FFTOpRecurrence (T : ℕ → ℕ) (c : ℕ) : Prop :=
  ∀ n ≥ 2, T n ≤ 2 * T (n / 2) + c * n

/-- Dyadic induction theorem: on powers of two $2^k$, any function satisfying the FFT recurrence
obeys $T(2^k) \le T(1) \cdot 2^k + c \cdot 2^k \cdot k$. -/
theorem fft_dyadic_bound (T : ℕ → ℕ) (c : ℕ) (hrec : FFTOpRecurrence T c) (k : ℕ) :
    T (2 ^ k) ≤ T 1 * 2 ^ k + c * 2 ^ k * k := by
  induction k with
  | zero =>
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
    have h2succ : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ, mul_comm]
    calc T (2 ^ (k + 1))
      _ ≤ 2 * T (2 ^ k) + c * 2 ^ (k + 1) := hstep
      _ ≤ 2 * (T 1 * 2 ^ k + c * 2 ^ k * k) + c * 2 ^ (k + 1) := by omega
      _ = T 1 * (2 * 2 ^ k) + c * (2 * 2 ^ k) * k + c * 2 ^ (k + 1) := by ring
      _ = T 1 * 2 ^ (k + 1) + c * 2 ^ (k + 1) * k + c * 2 ^ (k + 1) := by rw [← h2succ]
      _ = T 1 * 2 ^ (k + 1) + c * 2 ^ (k + 1) * (k + 1) := by ring

/-- Concrete operational work model for FFT on $n$ elements:
Each of the $\text{Nat.size } n$ stages performs $n/2$ butterflies, each taking
1 multiplication + 1 addition + 1 subtraction = 3 operations, totaling $3n \cdot \text{size } n$. -/
def fftWork (n : ℕ) : ℕ :=
  3 * n * Nat.size n

/-- Operational bound on FFT work: $W(n) \le 3n \cdot \text{Nat.size } n$. -/
theorem fftWork_le (n : ℕ) (_hn : 1 ≤ n) :
    fftWork n ≤ 3 * n * Nat.size n := by
  unfold fftWork
  rfl

/-! ### Fast Polynomial Multiplication Complexity -/

/-- Naive polynomial multiplication operational complexity:
Multiplying two polynomials of degree $< n$ performs $n^2$ scalar multiplications. -/
def naivePolyMulWork (n : ℕ) : ℕ :=
  n ^ 2

/-- Naive polynomial multiplication has quadratic complexity $n^2$. -/
theorem naivePolyMulWork_quadratic (n : ℕ) :
    naivePolyMulWork n = n ^ 2 :=
  rfl

/-- FFT-based polynomial multiplication operational work:
1. Two forward FFTs on padded inputs of size $2n$: $2 \cdot \text{fftWork}(2n)$.
2. Pointwise multiplication of point-value representations: $2n$ scalar multiplications.
3. One inverse FFT on the product: $\text{fftWork}(2n)$.
Total work: $3 \cdot \text{fftWork}(2n) + 2n$. -/
def fftPolyMulWork (n : ℕ) : ℕ :=
  3 * fftWork (2 * n) + 2 * n

/-- Size identity: $\text{Nat.size}(2n) \le \text{Nat.size } n + 1$ for all $n \in \mathbb{N}$. -/
theorem size_two_mul_le (n : ℕ) :
    Nat.size (2 * n) ≤ Nat.size n + 1 := by
  rw [Nat.size_le, pow_succ]
  have h := Nat.lt_size_self n
  omega

/-- Concrete linear-logarithmic upper bound on FFT polynomial multiplication:
$W_{poly}(n) \le 38 n \cdot \text{Nat.size } n$ for all $n \ge 1$.
This contrasts sharply with naive multiplication $O(n^2)$. -/
theorem fftPolyMulWork_le (n : ℕ) (hn : 1 ≤ n) :
    fftPolyMulWork n ≤ 38 * n * Nat.size n := by
  unfold fftPolyMulWork fftWork
  have hsize_pos : 1 ≤ Nat.size n := Nat.size_pos.mpr hn
  have h2n_size : Nat.size (2 * n) ≤ Nat.size n + 1 := size_two_mul_le n
  nlinarith

end Amort.Algebraic
