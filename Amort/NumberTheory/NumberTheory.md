# Number Theoretic Algorithms Architecture (`Amort.NumberTheory`)

This suite formalizes classical number theoretic algorithms in Lean 4:

1. **Fast Modular Exponentiation (Binary Exponentiation)** (`Amort/NumberTheory/ModExp.lean`):
   - **Repeated Squaring**: Tail-recursive state $(acc, base, exp)$.
   - **Correctness Invariant**: State preserves $acc \cdot base^{exp} \equiv a^b \pmod m$.
   - **Step Bound**: At most 2 multiplications per bit of exponent $b$, bounding total
     multiplications to $\le 2 \cdot \text{Nat.size } b = O(\log b)$.

2. **Extended Euclidean Algorithm** (`Amort/NumberTheory/ExtendedGCD.lean`):
   - **Bézout Identity**: Computes $x, y \in \mathbb{Z}$ satisfying $a \cdot x + b \cdot y = \gcd(a, b)$.
   - **Linear Combination Invariants**: Preserved inductively across all quotient division steps.
   - **Remainder Halving Theorem**: $2 \cdot r_{k+2} < r_k$ across two consecutive modulo steps.
   - **Logarithmic Step Bound**: $\le 2 \cdot \text{Nat.size}(\min(a, b)) + 1 = O(\log(\min(a, b)))$.

3. **Sieve of Eratosthenes** (`Amort/NumberTheory/Sieve.lean`):
   - **Composite Marking**: $k \in [2, n]$ is marked iff $k = m \cdot p$ with prime $p$ and $m \ge 2$.
   - **Correctness Theorem**: $k \in [2, n]$ is unmarked iff $k$ is prime.
   - **Harmonic Operational Bound**: $\sum_{p \le n} \lfloor n / p \rfloor \le n \sum_{k=1}^n (1 / k)
     \le n (1 + \ln n) = O(n \log n)$.

4. **Asymptotics** (`Amort/NumberTheory/Asymptotics.lean`):
   - Bridges connecting ModExp ($O(\log b)$), Extended GCD ($O(\log(\min(a, b)))$), and
     Sieve ($O(n \log n)$) to Mathlib `IsBigO` under `Filter.atTop`.
