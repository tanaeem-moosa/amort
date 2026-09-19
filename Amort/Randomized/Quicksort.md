# Expected Complexity of Randomized Quicksort

## Theoretical Foundations
Let $A = [a_1, \dots, a_n]$ be an array of $n$ distinct elements, with sorted order $z_1 < z_2 < \dots < z_n$. In randomized quicksort, pivots are chosen uniformly at random from the active subproblem.

For $1 \le i < j \le n$, define indicator variable $X_{ij} = 1$ if $z_i$ and $z_j$ are compared, and 0 otherwise.

### Pivot Selection Invariant
Elements $z_i$ and $z_j$ are compared if and only if the first pivot chosen from the set:
$$Z_{ij} = \{ z_i, z_{i+1}, \dots, z_j \}$$
is either $z_i$ or $z_j$.
- If an intermediate element $z_k$ ($i < k < j$) is chosen first, $z_i$ and $z_j$ fall into different partitions and are never compared.
- Since every element in $Z_{ij}$ has equal probability of being chosen first as a pivot:
  $$\mathbb{P}[X_{ij} = 1] = \frac{2}{j - i + 1}$$

### Linearity of Expectation & Distance Grouping
Total comparisons $C = \sum_{i=1}^{n-1} \sum_{j=i+1}^n X_{ij}$. By linearity of expectation:
$$\mathbb{E}[C] = \sum_{i=1}^{n-1} \sum_{j=i+1}^n \frac{2}{j - i + 1}$$

Grouping by distance $k = j - i \in \{1, \dots, n-1\}$, there are $n - k$ pairs at distance $k$:
$$\mathbb{E}[C] = \sum_{k=1}^{n-1} (n - k) \frac{2}{k+1} \le 2n \sum_{k=1}^{n-1} \frac{1}{k+1} \le 2n H(n) = O(n \log n)$$
