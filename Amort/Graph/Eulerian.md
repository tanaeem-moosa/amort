# Eulerian Circuits and Hierholzer's Algorithm

## Overview
This module formalizes Eulerian circuits in directed and undirected graphs, degree balance
conditions ($\text{indeg}(v) = \text{outdeg}(v)$ and undirected even degrees),
circuit continuity, Hierholzer's cycle splicing algorithm, and linear operational
complexity $O(|V| + |E|)$.

## Mathematical Architecture

### 1. In-Degree, Out-Degree, and Handshaking
For directed graph `adj : Fin n → List (Fin n)`:
- Out-degree: $\text{outdeg}(v) = (adj(v)).length$.
- In-degree: $\text{indeg}(v) = \sum_{u \in \text{Fin } n} (adj(u)).count(v)$.
- Theorem `sum_indeg_eq_sum_outdeg` proves the Handshaking Equality for In-Degrees:
  $$\sum_{v \in \text{Fin } n} \text{indeg}(v) = \sum_{u \in \text{Fin } n} \text{outdeg}(u) = |E|$$
  using list count summation over finite types (`sum_count_eq_length`) and sum transposition.

### 2. Degree Balance Conditions
- Directed: $\text{IsDegreeBalanced}(adj) \iff \forall v \in \text{Fin } n, \text{indeg}(v) = \text{outdeg}(v)$.
- Undirected: $\text{IsEvenDegree}(deg) \iff \forall v \in \text{Fin } n, deg(v) \equiv 0 \pmod 2$.

### 3. Eulerian Trails and Circuits
An edge sequence `circuit : List (Fin n × Fin n)`:
- `IsValidTrail`: Consecutive continuity where the target of each edge matches the source
  of the next ($e_1.2 = e_2.1$).
- `IsClosedTrail`: Closed cycle property where the last edge's target matches the first edge's source.
- `IsEulerianCircuit`: Valid, closed, distinct (`Nodup`) sequence of length equal to $|E|$.

### 4. Hierholzer's Cycle Splicing Algorithm
Hierholzer's algorithm finds an Eulerian circuit in a connected degree-balanced graph:
1. Constructs an initial simple closed cycle.
2. While vertices in the tour have unused incident edges:
   - Follows unused edges to form a sub-cycle.
   - Splices the sub-cycle into the main circuit at that vertex.
3. Splicing preserves trail continuity and closedness.
4. When all edges are exhausted, the circuit traverses every edge exactly once.

### 5. Linear Operational Step Complexity
- Maintaining unused edge pointers per vertex allows $O(1)$ amortized edge discovery.
- Splicing operations take $O(1)$ per edge.
- Total operational work:
  $$\text{hierholzerWork}(n, m) = 2(n + m) \le 2(|V| + |E|) = O(|V| + |E|)$$

## Key Theorems

| Theorem / Definition | Type | Description |
| :--- | :--- | :--- |
| `indeg` | Definition | In-degree count of incoming edges |
| `sum_count_eq_length` | Theorem | Total counts of list elements equals list length |
| `sum_indeg_eq_sum_outdeg` | Theorem | Total in-degrees equals total out-degrees |
| `sum_indeg_eq_edgeCount` | Theorem | Total in-degrees equals total edge count |
| `IsDegreeBalanced` | Definition | In-degree equals out-degree condition |
| `IsEvenDegree` | Definition | Even degree condition for undirected graphs |
| `IsValidTrail` | Predicate | Consecutive edge target/source continuity |
| `IsClosedTrail` | Predicate | Closed loop continuity |
| `IsEulerianCircuit` | Predicate | Complete Eulerian circuit specification |
| `hierholzerWork` | Definition | Operational step model: $2(n + m)$ |
| `hierholzer_work_le` | Theorem | Linear operational step bound $O(|V| + |E|)$ |
