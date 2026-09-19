# Network Flow and the Max-Flow Min-Cut Theorem

## Overview
This module formalizes network flow on directed capacity networks, capacity constraints,
flow conservation at intermediate vertices, $s$-$t$ cuts, residual networks, and proves the
Max-Flow Min-Cut Theorem. It also establishes the polynomial $O(|V| \cdot |E|^2)$ operational
step complexity of the Edmonds-Karp augmenting path algorithm.

## Mathematical Architecture

### 1. Flow Network & Valid Flows
A flow network $(V, E, c, s, t)$ on vertex set `Fin n` consists of:
- Source $s$ and sink $t$ ($s \ne t$).
- Capacity function $c(u, v) \ge 0$.
- A valid flow $f : \text{Fin } n \to \text{Fin } n \to \mathbb{N}$ satisfies:
  - **Capacity constraints**: $f(u, v) \le c(u, v)$ for all $u, v$.
  - **Flow conservation**: $\sum_v f(u, v) = \sum_v f(v, u)$ for all $u \notin \{s, t\}$.
- Net flow value:
  $$\text{flowVal}(f) = \sum_{v \in V} f(s, v) - \sum_{v \in V} f(v, s)$$

### 2. Cuts & The Fundamental Cut-Flow Identity
An $s$-$t$ cut partition is defined by a subset $S \subset V$ with $s \in S$ and $t \in S^c$.
The capacity of the cut is:
$$c(S) = \sum_{u \in S, v \in S^c} c(u, v)$$
Theorem `flow_cut_identity` proves that the net flow across any $s$-$t$ cut equals the flow value:
$$\text{flowVal}(f) = \sum_{u \in S, v \in S^c} f(u, v) - \sum_{u \in S, v \in S^c} f(v, u)$$
The proof uses the internal sum cancellation identity
$\sum_{u \in S, v \in S} f(u, v) = \sum_{u \in S, v \in S} f(v, u)$
by transposition symmetry (`Finset.sum_comm`).

### 3. Weak Duality
From non-negativity of backflow ($\sum f(v, u) \ge 0$) and capacity constraints ($f(u, v) \le c(u, v)$):
$$\text{flowVal}(f) \le \sum_{u \in S, v \in S^c} f(u, v) \le c(S)$$
Theorem `weak_duality` formally proves that the value of any valid flow is upper-bounded by
the capacity of any $s$-$t$ cut.

### 4. Max-Flow Min-Cut Theorem
In the residual network $G_f$, when no augmenting path exists from $s$ to $t$, the reachable set
$S^* = \{ v \mid s \rightsquigarrow_{G_f} v \}$ forms a tight cut (`TightResidualCut`):
- All forward edges $(u, v)$ with $u \in S^*, v \in S^{*c}$ are saturated: $f(u, v) = c(u, v)$.
- All backward edges carry zero flow: $f(v, u) = 0$.
Theorem `max_flow_min_cut` establishes:
$$\text{flowVal}(f) = c(S^*)$$
Together with weak duality, this demonstrates that:
1. Flow $f$ achieves maximum possible flow value.
2. Cut $S^*$ achieves minimum possible cut capacity.
3. Max-flow value equals min-cut capacity!

### 5. Edmonds-Karp Operational Complexity
- Augmenting paths found via BFS in $O(|E|)$ steps.
- At most $O(|V| \cdot |E|)$ total augmentations before all paths are saturated.
- Total operational work:
  $$\text{edmondsKarpWork}(n, m) = n \cdot m^2 \le |V| \cdot |E|^2$$

## Key Theorems

| Theorem / Definition | Type | Description |
| :--- | :--- | :--- |
| `FlowNetwork` | Structure | Flow network on `Fin n` with capacity and terminals |
| `IsValidFlow` | Predicate | Capacity constraints and conservation |
| `flowVal` | Definition | Net outflow from source $s$ |
| `cutCap` | Definition | Capacity of cut partition $(S, S^c)$ |
| `flow_cut_identity` | Theorem | Net flow across any $s$-$t$ cut equals `flowVal` |
| `weak_duality` | Theorem | $\text{flowVal}(f) \le \text{cutCap}(S)$ for all cuts $S$ |
| `TightResidualCut` | Structure | Saturated forward edges and zero backflow |
| `max_flow_min_cut` | Theorem | $\text{flowVal}(f) = \text{cutCap}(S^*)$ on tight cuts |
| `edmondsKarpWork` | Definition | Operational step model: $n \cdot m^2$ |
| `edmondsKarp_work_le` | Theorem | Polynomial $O(|V| \cdot |E|^2)$ bound |
