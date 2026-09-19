# Extended Euclidean Algorithm & Bézout Invariants

## Bézout Identity
For any $a, b \in \mathbb{N}$, `extGCD a b` computes $(x, y, g)$ satisfying:
$$a \cdot x + b \cdot y = g \quad \text{and} \quad g = \gcd(a, b)$$

## Inductive Step
From division $a = q \cdot b + r$:
If $b \cdot s + r \cdot t = g$, substituting $r = a - q \cdot b$ yields:
$$a \cdot t + b \cdot (s - q \cdot t) = g$$

## Remainder Halving
For positive $b \le a$, $a \bmod b \le a / 2$, so $2 \cdot (a \bmod b) < a$.
Consequently, in any two successive modulo steps, the remainder strictly halves:
$$2 \cdot r_{k+2} < r_k$$
Bounding the total number of division steps by $2 \cdot \text{Nat.size}(\min(a, b)) + 1 = O(\log(\min(a, b)))$.
