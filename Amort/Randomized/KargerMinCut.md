# Karger's Randomized Min-Cut Contraction Algorithm

> **Status: stub — not verified** (Phase 4 canon stub; contraction survival product is proven,
> but randomized graph contraction on PMF is a specification stub).


## Theoretical Foundations
In an undirected multigraph $G = (V, E)$ with $|V| = n$, a global minimum cut (min-cut) $(S, S^c)$ is a non-trivial partition minimizing the number of crossing edges $k = e(S, S^c)$.

### Degree and Edge Lower Bound
Every vertex $v$ defines a cut $(\{v\}, V \setminus \{v\})$, so $\text{deg}(v) \ge k$. By the Handshaking Lemma:
$$2|E| = \sum_{v \in V} \text{deg}(v) \ge n \cdot k \implies |E| \ge \frac{n \cdot k}{2}$$

### Single Contraction Step
An edge contraction merges endpoints $u, v$ and removes self-loops. If a uniformly chosen random edge $e \in E$ does not cross $(S, S^c)$, the cut survives. The probability of choosing a cut edge is:
$$\mathbb{P}[e \in (S, S^c)] = \frac{k}{|E|} \le \frac{k}{n k / 2} = \frac{2}{n}$$
Thus the cut survives with probability at least $1 - \frac{2}{n} = \frac{n - 2}{n}$.

### Telescoping Product
After $n - 2$ successive contractions down to 2 super-vertices, the conditional survival probability telescopes:
$$\mathbb{P}[\text{success}] \ge \prod_{i=0}^{n-3} \frac{n - i - 2}{n - i} = \frac{n-2}{n} \cdot \frac{n-3}{n-1} \cdot \dots \cdot \frac{2}{4} \cdot \frac{1}{3} = \frac{2}{n(n-1)}$$

### Amplification
Repeating the algorithm $T = \binom{n}{2} \ln(1/\delta)$ times reduces the failure probability to:
$$(1 - p)^T \le e^{-p T} \le \delta$$
