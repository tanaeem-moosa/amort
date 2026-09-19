# Randomized Algorithms & Probabilistic Complexity in Lean 4

This module family formalizes probabilistic complexity analysis and randomized algorithms:

1. **Expected Complexity of Randomized Quicksort** (`Quicksort.lean`):
   - Indicator variables $X_{ij}$ for comparisons between elements $z_i$ and $z_j$.
   - Pivot selection invariant: $z_i$ and $z_j$ are compared iff the first pivot chosen from
     $\{z_i, \dots, z_j\}$ is $z_i$ or $z_j$.
   - Pivot probability lemma: $\mathbb{P}[X_{ij} = 1] = \frac{2}{j - i + 1}$.
   - Distance grouping: $\mathbb{E}[C] = \sum_{k=1}^{n-1} \frac{2(n-k)}{k+1} \le 2n H(n) = O(n \log n)$.

2. **Karger's Min-Cut Contraction Algorithm** (`KargerMinCut.lean`):
   - Multigraph random edge contraction.
   - Degree and edge lower bounds: min-cut size $k \implies |E| \ge n k / 2$.
   - Contraction survival probability: single contraction avoids min-cut with probability $\ge (n-2)/n$.
   - Telescoping product lower bound: success probability after $n-2$ contractions is $\ge \frac{2}{n(n-1)}$.
   - Repetition amplification: $O(n^2)$ trials reduce failure probability below $\delta$.

3. **Universal Hashing & Reservoir Sampling** (`UniversalHash.lean`):
   - 2-Universal hash families: $\forall x \ne y, \mathbb{P}[h(x) = h(y)] \le 1/m$.
   - Expected hash table collisions $\le n/m$, yielding $O(1)$ expected lookup.
   - Reservoir stream sampling: maintaining uniform sample of size $k$ across stream of size $N$.
   - Streaming invariant induction: item survival probability $\frac{k}{t} \cdot \frac{t}{t+1} = \frac{k}{t+1}$.

4. **Asymptotic Complexity Bridges** (`Asymptotics.lean`):
   - Connection of Quicksort, Karger, and Universal Hashing bounds to Mathlib's `Mathlib.Analysis.Asymptotics.IsBigO`.
