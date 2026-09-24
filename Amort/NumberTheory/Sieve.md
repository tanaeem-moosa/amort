# Sieve of Eratosthenes & Harmonic Complexity

> **Status: stub — not verified** (Phase 3 canon stub; prime characterization is proven,
> but operational array composite marking sieve is a specification stub).


## Correctness Theorem
An integer $k \ge 2$ remains unmarked by the composite marking sieve iff $k$ is prime.
- Composite numbers $k \ge 2$ have a prime factor $p$ with $k = m \cdot p$ and $m \ge 2$, hence marked.
- Primes cannot be factored as $m \cdot p$ with $m \ge 2$ and prime $p$, hence remain unmarked.

## Harmonic Work Bound
Each prime $p \le n$ generates at most $\lfloor n / p \rfloor$ marks.
$$\sum_{p \le n} \frac{n}{p} \le n \sum_{k=1}^n \frac{1}{k} \le n (1 + \ln n) = O(n \log n)$$
Concrete operational work $W(n) = n \cdot \text{Nat.size } n + n \le 2n \cdot \text{Nat.size } n$.
