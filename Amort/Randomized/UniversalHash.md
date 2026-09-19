# 2-Universal Hashing and Reservoir Sampling

## 2-Universal Hash Families
A finite family $\mathcal{H}$ of hash functions $h : U \to \{0, \dots, m-1\}$ is 2-Universal if for all distinct $x \ne y \in U$:
$$\mathbb{P}_{h \in \mathcal{H}}[h(x) = h(y)] = \frac{|\{ h \in \mathcal{H} \mid h(x) = h(y) \}|}{|\mathcal{H}|} \le \frac{1}{m}$$

For a dictionary storing $n$ elements in $m$ buckets, the expected number of collisions for any element $x$ is:
$$\mathbb{E}[\text{collisions}] = \sum_{y \in S, y \ne x} \mathbb{P}[h(x) = h(y)] \le \frac{n}{m} = \alpha$$
When $m = \Omega(n)$, expected collisions $\le 1$, giving $O(1)$ expected lookup and insertion times.

## Reservoir Sampling
Given a stream $x_1, x_2, \dots, x_N$ of unknown or infinite length, reservoir sampling maintains a uniform random sample of size $k \le N$ in $O(k)$ memory.

### Algorithm
1. Store the first $k$ items in reservoir $R$.
2. For each incoming item $x_{t+1}$ ($t \ge k$):
   - With probability $k / (t + 1)$, include $x_{t+1}$ by replacing a uniformly chosen item in $R$.
   - With probability $1 - k / (t + 1)$, discard $x_{t+1}$.

### Streaming Invariant Induction
By induction on $t$:
- Base case $t = k$: all items are in $R$ with probability $k/k = 1$.
- Inductive step $t \to t+1$:
  - New item $x_{t+1}$ is included with probability $k / (t + 1)$.
  - Any previously included item $x_i$ survives if not chosen as victim:
    $$\mathbb{P}[x_i \in R_{t+1}] = \frac{k}{t} \cdot \left(1 - \frac{k}{t+1} \cdot \frac{1}{k}\right) = \frac{k}{t} \cdot \frac{t}{t+1} = \frac{k}{t+1}$$
This proves that every stream item has equal probability $k / N$ of being retained.
