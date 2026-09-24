# Fast Fourier Transform (FFT) & Polynomial Multiplication

> **Status: stub — not verified** (Phase 3 canon stub; Cooley-Tukey decomposition is proven,
> but recursive list FFT execution and DFT equivalence are specification stubs).


## 1. Overview and Problem Statement

Polynomial multiplication is a fundamental algebraic primitive in computer science, computer algebra,
and digital signal processing. Given two degree-$n$ polynomials
$$A(x) = \sum_{j=0}^{n-1} a_j x^j, \quad B(x) = \sum_{j=0}^{n-1} b_j x^j$$
their product $C(x) = A(x) \cdot B(x)$ has degree $\le 2n - 2$, with coefficients given by the Cauchy
convolution:
$$c_k = \sum_{j=0}^k a_j b_{k-j}$$
Computing all $2n - 1$ coefficients naively requires $\Theta(n^2)$ scalar multiplications and additions.

The Fast Fourier Transform (FFT), discovered in its modern radix-2 form by J. W. Cooley and J. W. Tukey
(1965), enables polynomial multiplication in $O(n \log n)$ operations by converting between
coefficient representations and point-value representations via evaluation at complex roots of unity.

---

## 2. Mathematical Architecture

### 2.1 Roots of Unity & Invariant Lemmas

Let $R$ be a commutative ring. An element $\omega \in R$ is an $n$-th root of unity if:
$$\text{IsNthRootOfUnity}(\omega, n) \iff \omega^n = 1$$

Three core lemmas govern the algebraic symmetry of roots of unity:

1. **Cancellation Lemma** (`rootOfUnity_cancellation`, `rootOfUnity_pow_order`):
   For any $d, k, n \in \mathbb{N}$:
   $$(\omega^d)^k = \omega^{d \cdot k}$$
   If $\omega$ is a $(d \cdot n)$-th root of unity, then $\omega^d$ is an $n$-th root of unity:
   $$(\omega^d)^n = \omega^{d \cdot n} = 1$$

2. **Halving Lemma** (`halving_lemma`, `halving_lemma_sq`):
   When $n = 2m$ and $\omega^{2m} = 1$, the squares of the $n$ roots of unity yield the $m$ roots of unity:
   $$(\omega^k)^2 = (\omega^2)^k$$
   $$(\omega^{k + m})^2 = \omega^{2k + 2m} = \omega^{2k} \cdot \omega^{2m} = \omega^{2k} \cdot 1 = (\omega^2)^k$$

3. **Negation / Symmetry Lemma** (`negation_lemma`):
   When $\omega^m = -1$ (as in the complex field where $e^{i \pi} = -1$):
   $$\omega^{k + m} = \omega^k \cdot \omega^m = - \omega^k$$

---

### 2.2 Cooley-Tukey Radix-2 Polynomial Decomposition

To evaluate $A(x) = \sum_{j=0}^{n-1} a_j x^j$ of even length $n = 2m$, partition the coefficient list
into even-indexed and odd-indexed sublists:
$$A_{even}(y) = \sum_{j=0}^{m-1} a_{2j} y^j, \quad A_{odd}(y) = \sum_{j=0}^{m-1} a_{2j+1} y^j$$

**Fundamental Decomposition Theorem** (`cooley_tukey_decomp`):
For any $x \in R$:
$$A(x) = A_{even}(x^2) + x \cdot A_{odd}(x^2)$$

*Proof in Lean 4*: Formalized by structural two-step induction (`list_two_step_induction`) on the
coefficient list $l$. In the inductive step $a :: b :: rest$, Horner evaluation expands to:
$$a + x \cdot b + x^2 \cdot (A_{even}(x^2) + x \cdot A_{odd}(x^2)) = a + x \cdot b + x^2 \cdot \text{evalPoly}(rest, x)$$
which rings identically to $\text{evalPoly}(a :: b :: rest, x)$.

---

### 2.3 Butterfly Operations & DFT Point Evaluation

The Discrete Fourier Transform of vector $a$ of length $n$ with respect to root of unity $\omega$ is:
$$\text{DFT}_n(a)_k = A(\omega^k) = \sum_{j=0}^{n-1} a_j (\omega^k)^j \quad (0 \le k < n)$$

For $k < m = n/2$, the Cooley-Tukey decomposition reduces evaluation to the smaller subproblems
$u_k = A_{even}((\omega^2)^k)$ and $v_k = A_{odd}((\omega^2)^k)$:

1. **Even Part** (`butterfly_correctness_even_part`):
   $$A(\omega^k) = A_{even}((\omega^k)^2) + \omega^k A_{odd}((\omega^k)^2) = u_k + \omega^k v_k$$
2. **Mirrored Part** (`butterfly_correctness_odd_part`):
   $$A(\omega^{k + m}) = A_{even}((\omega^{k + m})^2) + \omega^{k + m} A_{odd}((\omega^{k + m})^2) = u_k - \omega^k v_k$$

The **Butterfly Operation** (`butterfly`) computes:
$$\text{butterfly}(u_k, v_k, \omega^k) = (u_k + \omega^k v_k, \; u_k - \omega^k v_k) = (A(\omega^k), \; A(\omega^{k+m}))$$
Thus, a single twiddle factor multiplication $\omega^k v_k$ and two additions/subtractions simultaneously
yield both mirrored output values.

---

### 2.4 Recurrence Relations and Operational Step Bounds

The Radix-2 divide-and-conquer recurrence on problem size $n$ satisfies:
$$T(n) \le 2 T(n / 2) + c \cdot n \quad (n \ge 2)$$

- **Dyadic Induction Theorem** (`fft_dyadic_bound`):
  For $n = 2^k$:
  $$T(2^k) \le T(1) \cdot 2^k + c \cdot 2^k \cdot k$$
- **Operational Work Model** (`fftWork`):
  Across all $\text{Nat.size } n$ stages, $n/2$ butterflies at 3 operations each yield:
  $$W_{FFT}(n) = 3n \cdot \text{Nat.size } n \le 3n \cdot \text{size } n$$

---

### 2.5 Fast Polynomial Multiplication

To multiply polynomials $A, B$ of degree $< n$:
1. Pad coefficient vectors to length $2n$.
2. Compute point evaluations $\hat{A} = \text{FFT}_{2n}(A)$ and $\hat{B} = \text{FFT}_{2n}(B)$ (cost: $2 \cdot W_{FFT}(2n)$).
3. Compute pointwise products $\hat{C}_k = \hat{A}_k \cdot \hat{B}_k$ (cost: $2n$).
4. Compute inverse FFT $\text{IFFT}_{2n}(\hat{C})$ (cost: $W_{FFT}(2n)$).

**Total Operational Work** (`fftPolyMulWork`):
$$W_{poly}(n) = 3 \cdot W_{FFT}(2n) + 2n \le 38 n \cdot \text{Nat.size } n$$
proven in `fftPolyMulWork_le` using the bit-size doubling bound $\text{Nat.size}(2n) \le \text{Nat.size } n + 1$.

---

## 3. Lean 4 Formalization Index

| Theorem / Definition | File | Description | Axioms |
| :--- | :--- | :--- | :--- |
| `IsNthRootOfUnity` | `Amort/Algebraic/FFT.lean` | Root of unity predicate $\omega^n = 1$ | foundational |
| `rootOfUnity_cancellation` | `Amort/Algebraic/FFT.lean` | Cancellation lemma $(\omega^d)^k = \omega^{dk}$ | foundational |
| `halving_lemma` | `Amort/Algebraic/FFT.lean` | $(\omega^{k+m})^2 = (\omega^2)^k$ when $\omega^{2m} = 1$ | foundational |
| `negation_lemma` | `Amort/Algebraic/FFT.lean` | $\omega^{k+m} = -\omega^k$ when $\omega^m = -1$ | foundational |
| `evalPoly` | `Amort/Algebraic/FFT.lean` | Horner polynomial evaluation | foundational |
| `cooley_tukey_decomp` | `Amort/Algebraic/FFT.lean` | $A(x) = A_{even}(x^2) + x A_{odd}(x^2)$ | `[propext, Quot.sound]` |
| `butterfly` | `Amort/Algebraic/FFT.lean` | Radix-2 butterfly operator $(u + \omega v, u - \omega v)$ | foundational |
| `butterfly_dft_pair` | `Amort/Algebraic/FFT.lean` | Butterfly produces $A(\omega^k)$ and $A(\omega^{k+m})$ | `[propext, Quot.sound]` |
| `fft_dyadic_bound` | `Amort/Algebraic/FFT.lean` | $T(2^k) \le T(1) 2^k + c 2^k k$ | `[propext, Quot.sound]` |
| `fftWork_le` | `Amort/Algebraic/FFT.lean` | FFT operational work $3n \cdot \text{size } n$ | foundational |
| `fftPolyMulWork_le` | `Amort/Algebraic/FFT.lean` | FFT poly mul bound $\le 38n \cdot \text{size } n$ | `[propext, Classical.choice, Quot.sound]` |
