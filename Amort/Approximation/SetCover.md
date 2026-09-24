# Set Cover Greedy $H(n)$-Approximation via Harmonic Potential

> **Status: stub — not verified** (Phase 4 canon stub; harmonic charging scheme is proven,
> but operational greedy subset extraction is a specification stub).

## Theoretical Foundations
Given a universe $U$ of size $n$ and a family of subsets $\mathcal{S}$, the Set Cover problem seeks a minimum-size subcollection $\mathcal{C} \subseteq \mathcal{S}$ that covers $U$.

The greedy heuristic iteratively selects a set $S \in \mathcal{S}$ that covers the maximum number of currently uncovered elements. When a set covers $k$ new elements, each new element $x$ is charged a price:
$$\text{price}(x) = \frac{1}{k}$$

The total cost of the greedy cover equals the sum of all element prices:
$$|\mathcal{C}_{\text{greedy}}| = \sum_{x \in U} \text{price}(x)$$

For any set $S^* \in \mathcal{C}^*$ from an optimal cover, when its elements are covered in sequence, the $j$-th from last element is covered when at least $j$ elements of $S^*$ remain uncovered. Since $S^*$ was available, the greedy choice covered at least $j$ elements, charging at most $1/j$. Summing over $S^*$:
$$\sum_{x \in S^*} \text{price}(x) \le \sum_{j=1}^{|S^*|} \frac{1}{j} = H(|S^*|) \le H(n)$$

Summing over all sets in $\mathcal{C}^*$ yields:
$$|\mathcal{C}_{\text{greedy}}| \le \sum_{S^* \in \mathcal{C}^*} H(n) = H(n) \cdot |\mathcal{C}^*| = H(n) \cdot \text{OPT}$$

## Formalization Highlights
- `Amort.Approximation.harmonic`: Formal $n$-th harmonic number $\sum_{i=0}^{n-1} \frac{1}{i+1}$.
- `Amort.Approximation.harmonic_monotone`: Monotonicity of harmonic numbers.
- `Amort.Approximation.HarmonicCharging`: Encapsulation of the marginal charging scheme.
- `Amort.Approximation.set_cover_approx_bound`: Rigorous proof that greedy size is bounded by $H(n) \cdot \text{OPT}$.
