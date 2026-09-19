# Strassen's Sub-Cubic Matrix Multiplication

## 1. Overview and Problem Statement

Matrix multiplication is central to linear algebra, scientific computing, and algorithmic graph theory.
Given two $n \times n$ matrices $A$ and $B$, standard matrix multiplication computes the $n^2$ entries
of $C = A \cdot B$ via:
$$C_{ij} = \sum_{k=1}^n A_{ik} B_{kj}$$
Each entry requires $n$ multiplications and $n - 1$ additions, totaling $n^3$ multiplications and
$n^2(n - 1)$ additions, giving cubic complexity $\Theta(n^3)$.

For decades, cubic complexity was believed to be optimal. In 1969, Volker Strassen published
*Gaussian Elimination is not Optimal*, demonstrating that $2 \times 2$ block matrices can be multiplied
using only **7 recursive multiplications** rather than 8. Applied recursively to $n \times n$ matrices,
this reduces operational complexity to:
$$T(n) \le 7 T(n / 2) + c \cdot n^2 \implies T(n) = O(n^{\log_2 7}) \approx O(n^{2.807})$$

---

## 2. Mathematical Architecture

### 2.1 $2 \times 2$ Block Matrix Representation

Let $R$ be an arbitrary ring (not necessarily commutative). A $2 \times 2$ block matrix is modeled by:
$$\begin{pmatrix} A_{11} & A_{12} \\ A_{21} & A_{22} \end{pmatrix}$$
where each block may itself be an $(n/2) \times (n/2)$ submatrix. Because matrix multiplication over
submatrices does not commute, algebraic equivalence of the formulas must hold in any non-commutative
ring.

Standard multiplication (`Matrix2x2.mul`) computes:
$$\begin{pmatrix} C_{11} & C_{12} \\ C_{21} & C_{22} \end{pmatrix} =
\begin{pmatrix} A_{11} B_{11} + A_{12} B_{21} & A_{11} B_{12} + A_{12} B_{22} \\
                A_{21} B_{11} + A_{22} B_{21} & A_{21} B_{12} + A_{22} B_{22} \end{pmatrix}$$
which directly requires 8 sub-multiplications.

---

### 2.2 Strassen's 7 Multiplications

Strassen constructs 7 clever auxiliary multiplications $M_1, \dots, M_7$ from linear combinations of blocks:

1. $M_1 = (A_{11} + A_{22}) \cdot (B_{11} + B_{22})$
2. $M_2 = (A_{21} + A_{22}) \cdot B_{11}$
3. $M_3 = A_{11} \cdot (B_{12} - B_{22})$
4. $M_4 = A_{22} \cdot (B_{21} - B_{11})$
5. $M_5 = (A_{11} + A_{12}) \cdot B_{22}$
6. $M_6 = (A_{21} - A_{11}) \cdot (B_{11} + B_{12})$
7. $M_7 = (A_{12} - A_{22}) \cdot (B_{21} + B_{22})$

---

### 2.3 Block Reconstruction & Algebraic Equivalence

The four product blocks are reconstructed from $M_1, \dots, M_7$ using purely additive operations:

- **Block (1, 1)**: $C_{11} = M_1 + M_4 - M_5 + M_7$
  $$\begin{aligned}
  &= (A_{11} + A_{22})(B_{11} + B_{22}) + A_{22}(B_{21} - B_{11}) - (A_{11} + A_{12})B_{22} + (A_{12} - A_{22})(B_{21} + B_{22}) \\
  &= A_{11} B_{11} + A_{12} B_{21}
  \end{aligned}$$
- **Block (1, 2)**: $C_{12} = M_3 + M_5$
  $$= A_{11}(B_{12} - B_{22}) + (A_{11} + A_{12})B_{22} = A_{11} B_{12} + A_{12} B_{22}$$
- **Block (2, 1)**: $C_{21} = M_2 + M_4$
  $$= (A_{21} + A_{22})B_{11} + A_{22}(B_{21} - B_{11}) = A_{21} B_{11} + A_{22} B_{21}$$
- **Block (2, 2)**: $C_{22} = M_1 - M_2 + M_3 + M_6$
  $$\begin{aligned}
  &= (A_{11} + A_{22})(B_{11} + B_{22}) - (A_{21} + A_{22})B_{11} + A_{11}(B_{12} - B_{22}) + (A_{21} - A_{11})(B_{11} + B_{12}) \\
  &= A_{21} B_{12} + A_{22} B_{22}
  \end{aligned}$$

**Theorem** (`strassen_mul_eq_std_mul`):
In any ring $R$:
$$\text{strassenMul}(A, B) = \text{mul}(A, B)$$
Formally verified in Lean 4 via `noncomm_ring`.

---

### 2.4 Recurrence Relations and Sub-Cubic Bound

Let $T(n)$ denote the operations to multiply two $n \times n$ matrices. Strassen's algorithm performs:
- 7 recursive multiplications of $(n/2) \times (n/2)$ matrices.
- 18 matrix additions/subtractions of $(n/2) \times (n/2)$ matrices, requiring $18 \cdot (n/2)^2 = 4.5 n^2$ additions.

This establishes the divide-and-conquer recurrence:
$$T(n) \le 7 T(n / 2) + c \cdot n^2 \quad (n \ge 2)$$

#### Closed-Form Geometric Solution
Unrolling $k$ levels for $n = 2^k$ produces the geometric sum:
$$\sum_{j=0}^{k-1} 7^{k-1-j} 4^j = \frac{7^k - 4^k}{7 - 4} = \frac{7^k - 4^k}{3}$$
Formalized via `geomSum74`:
- Exact recurrence identity (`strassen_dyadic_exact`):
  $$T(2^k) \le 7^k T(1) + 4c \cdot \text{geomSum74}(k)$$
- Upper bound (`strassen_dyadic_bound`):
  Since $3 \cdot \text{geomSum74}(k) = 7^k - 4^k \le 7^k$, we have $\text{geomSum74}(k) \le 7^k / 3 \le 7^k / 2$, yielding:
  $$T(2^k) \le (T(1) + 2c) \cdot 7^k$$

#### Strict Sub-Cubic Exponent Theorem
The exponent $\alpha = \log_2 7 = \frac{\ln 7}{\ln 2}$ satisfies:
$$\log_2 7 < 3$$
*Proof in Lean 4* (`strassen_subcubic_exponent`):
Since $\ln 2 > 0$ and $7 < 8 = 2^3$, monotonicity of $\ln$ gives $\ln 7 < \ln(2^3) = 3 \ln 2$, hence
$\frac{\ln 7}{\ln 2} < 3$.

Numerically:
$$\log_2 7 \approx 2.8073549... < 3$$
This proves that Strassen's algorithm is strictly sub-cubic.

---

## 3. Lean 4 Formalization Index

| Theorem / Definition | File | Description | Axioms |
| :--- | :--- | :--- | :--- |
| `Matrix2x2` | `Amort/Algebraic/Strassen.lean` | $2 \times 2$ block matrix type | foundational |
| `Matrix2x2.mul` | `Amort/Algebraic/Strassen.lean` | Standard matrix product (8 sub-multiplications) | foundational |
| `Matrix2x2.M1` ... `M7` | `Amort/Algebraic/Strassen.lean` | Strassen's 7 auxiliary multiplications | foundational |
| `strassen_c11_eq` | `Amort/Algebraic/Strassen.lean` | Algebraic equivalence for block (1, 1) | `[propext]` |
| `strassen_c12_eq` | `Amort/Algebraic/Strassen.lean` | Algebraic equivalence for block (1, 2) | `[propext]` |
| `strassen_c21_eq` | `Amort/Algebraic/Strassen.lean` | Algebraic equivalence for block (2, 1) | `[propext]` |
| `strassen_c22_eq` | `Amort/Algebraic/Strassen.lean` | Algebraic equivalence for block (2, 2) | `[propext]` |
| `strassen_mul_eq_std_mul` | `Amort/Algebraic/Strassen.lean` | Complete product equivalence theorem | `[propext]` |
| `geomSum74_eq` | `Amort/Algebraic/Strassen.lean` | Closed form $3 \cdot S_k = 7^k - 4^k$ | foundational |
| `strassen_dyadic_bound` | `Amort/Algebraic/Strassen.lean` | $T(2^k) \le (T(1) + 2c) \cdot 7^k$ | `[propext, Quot.sound]` |
| `strassen_subcubic_exponent` | `Amort/Algebraic/Strassen.lean` | Rigorous proof that $\log_2 7 < 3$ | `[propext, Classical.choice, Quot.sound]` |
| `strassenWork_le_rpow` | `Amort/Algebraic/Asymptotics.lean` | Bound $W(n) \le 7 n^{\log_2 7}$ | `[propext, Classical.choice, Quot.sound]` |
| `isBigO_strassenWork_rpow` | `Amort/Algebraic/Asymptotics.lean` | Mathlib `IsBigO` under `Filter.atTop` | `[propext, Classical.choice, Quot.sound]` |
