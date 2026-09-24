# Hall's Marriage Theorem and Max-Flow Equivalence

> **Status: stub — not verified** (Phase 4 canon stub; Hall condition necessity is proven,
> but sufficiency reduction is a specification stub).


## Theoretical Foundations
Let $G = (L, R, E)$ be a finite bipartite graph. For any subset $S \subseteq L$, the collective neighborhood is defined as:
$$N(S) = \{ v \in R \mid \exists u \in S, (u, v) \in E \}$$

Hall's Marriage Condition asserts:
$$\forall S \subseteq L, \quad |S| \le |N(S)|$$

### Necessity
If $G$ admits a matching saturating $L$, there exists an injective function $f : L \to R$ with $(u, f(u)) \in E$. For any $S \subseteq L$, the image $f(S)$ is contained in $N(S)$. By injectivity, $|S| = |f(S)| \le |N(S)|$.

### Sufficiency via Max-Flow Min-Cut
Construct a flow network $N$:
- Source $s$ connected to every $u \in L$ with capacity 1.
- Sink $t$ with edges from every $v \in R$ to $t$ with capacity 1.
- Edges $(u, v) \in E$ directed from $L$ to $R$ with capacity $\infty$ (or 1).

Any $s$-$t$ cut with finite capacity partitions $L$ into $S \cup (L \setminus S)$ and $R$ into $T \cup (R \setminus T)$ such that $N(S) \subseteq T$. The capacity of this cut is:
$$\text{cap}(S_{\text{cut}}, T_{\text{cut}}) = (|L| - |S|) + |T| \ge (|L| - |S|) + |N(S)|$$

Under Hall's condition $|N(S)| \ge |S|$, so:
$$\text{cap}(S_{\text{cut}}, T_{\text{cut}}) \ge |L| - |S| + |S| = |L|$$

The trivial cut $(\{s\}, V \setminus \{s\})$ has capacity $|L|$. Hence the minimum cut capacity is exactly $|L|$. By the Max-Flow Min-Cut theorem, the maximum flow value is $|L|$. By integrality, this yields an $L$-saturating matching.
