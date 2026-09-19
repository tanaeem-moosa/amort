# 2D Convex Hull: Andrew's Monotone Chain

## Orientation Determinant
For points $p, q, r \in \mathbb{Z}^2$:
$$\text{cross}(p, q, r) = (q_x - p_x)(r_y - p_y) - (q_y - p_y)(r_x - p_x)$$
A turn $p \to q \to r$ is strictly counter-clockwise iff $\text{cross}(p, q, r) > 0$.

## Amortized Scanning Analysis
For each candidate point $p$ added to the stack:
- $k \ge 0$ non-left turn points are popped.
- Point $p$ is pushed onto the stack.
- Actual operations: $k + 1$.
- Potential $\Phi = \text{length}$. Change $\Delta \Phi = 1 - k$.
- Amortized cost: $A = (k + 1) + (1 - k) = 2$.
- Telescoping over $n$ points bounds total operations to $\le 2n$.
