# amort

AI-assisted formalization of time complexity and correctness of algorithms in Lean 4.

## Modules Overview

This repository formalizes algorithms and their computational complexity in `Amort/GCD/`, `Amort/Sorting/`, `Amort/Recurrence/`, `Amort/String/`, `Amort/DP/`, and `Amort/Graph/`:

### 1. Binary GCD (Stein's Algorithm)
- **Formal Definition & Termination**: `Nat.binaryGcd` with well-founded termination measure $a + b$.
- **Mathematical Equivalence**: `Nat.binaryGcd_eq_gcd` proving `∀ a b, binaryGcd a b = Nat.gcd a b`.
- **Step Counting & Bounds**: Companion `Nat.binaryGcdSteps` and instrumented `Nat.binaryGcdWithSteps`:
  - `binaryGcdSteps a b ≤ Nat.size a + Nat.size b`
  - `binaryGcdSteps a b ≤ 2 * Nat.size (a + b)`
- **Documentation**: Detailed architecture, invariant lemma DAG, and proof notes in [`Amort/GCD/BinaryGCD.md`](Amort/GCD/BinaryGCD.md).

### 2. Euclidean GCD Step Counting & Modulo Halving
- **Step Counter**: `Nat.euclideanGcdSteps` mirroring `Nat.gcd.eq_def`.
- **Modulo Halving Property**: `Nat.mod_two_mul_lt` ($2 \cdot (a \bmod b) < a$ when $0 < b \le a$) and bit-size reduction `Nat.size_mod_add_one_le`.
- **Logarithmic Upper Bounds**:
  - `euclideanGcdSteps a b ≤ 2 * Nat.size (min a b) + 1`
  - `euclideanGcdSteps a b ≤ 2 * Nat.size (a + b) + 1`

### 3. GCD Mathlib Asymptotics Bridge (`Asymptotics.IsBigO`)
- **Universal Filters**: `isBigO_binaryGcdSteps_size_add` establishing $O(\text{size}(a + b))$ under arbitrary filters $l$.
- **Canonical Top & Measure Filters**:
  - `isBigO_binaryGcdSteps_atTop` under `Filter.atTop` on `ℕ × ℕ`.
  - `isBigO_binaryGcdSteps_comap_add_atTop` under pullback along $a + b$.
  - `isBigO_binaryGcdSteps_comap_size_atTop` under pullback along $\text{size}(a + b)$.
  - `isBigO_euclideanGcdSteps_atTop` establishing $O(\text{size}(\min a b))$ under `Filter.atTop`.
  - `isBigO_euclideanGcdSteps_comap_min_atTop` under pullback along $\min(a, b)$.
  - `isBigO_euclideanGcdSteps_comap_add_atTop` under pullback along $a + b$.
- **Documentation**: Comprehensive documentation in [`Amort/GCD/EuclideanAndAsymptotics.md`](Amort/GCD/EuclideanAndAsymptotics.md).

### 4. Insertion Sort Comparison Counting & $O(n^2)$ Complexity
- **Comparison Models**: `List.orderedInsertCount` and instrumented `List.orderedInsertWithCount`; `List.insertionSortCount` and instrumented `List.insertionSortWithCount`.
- **Mathlib Equivalence**: `(insertionSortWithCount r l).1 = List.insertionSort r l` and `(insertionSortWithCount r l).2 = insertionSortCount r l`.
- **Concrete Upper Bounds**:
  - `orderedInsertCount r a l ≤ l.length`
  - `insertionSortCount r l ≤ l.length * (l.length - 1) / 2`
  - `insertionSortCount r l ≤ l.length ^ 2`
- **Asymptotics**: `isBigO_insertionSortCount_sq` ($O(n^2)$ under arbitrary filters and `Filter.comap List.length Filter.atTop`) and `isBigO_insertionSort_triangular_atTop`.
- **Documentation**: Detailed proof strategy in [`Amort/Sorting/InsertionSort.md`](Amort/Sorting/InsertionSort.md).

### 5. Merge Sort Comparison Counting & $O(n \log n)$ Complexity
- **Comparison Models**: `List.mergeCount` and instrumented `List.mergeWithCount`; `List.mergeSortCount` and instrumented `List.mergeSortWithCount`.
- **Mathlib & Core Equivalence**: `(mergeSortWithCount le xs).1 = List.mergeSort xs le` and connection to Mathlib `List.insertionSort` for linear orders (`mergeSortWithCount_fst_eq_insertionSort`).
- **Recurrence & Bounds**:
  - `mergeCount le xs ys ≤ xs.length + ys.length`
  - Divide-and-conquer recurrence bound: `mergeSortRecBound n ≤ n * k` whenever $n \le 2^k$.
  - Bit-size logarithmic bound: `mergeSortRecBound n ≤ n * Nat.size n`.
  - Concrete list comparison bound: `mergeSortCount le xs ≤ xs.length * Nat.size xs.length`.
- **Asymptotics**: `isBigO_mergeSortCount_mul_size` ($O(n \cdot \text{size } n)$ under arbitrary filters and `Filter.comap List.length Filter.atTop`) and `isBigO_mergeSortRecBound_atTop` under `Filter.atTop`.
- **Documentation**: Detailed proof strategy in [`Amort/Sorting/MergeSort.md`](Amort/Sorting/MergeSort.md).

### 6. Comparison Sorting Lower Bound ($\Omega(n \log n)$)
- **Decision Tree Model**: `Amort.Sorting.DecisionTree` with depth and leaf count, proving `leafCount T ≤ 2 ^ depth T` by structural induction.
- **Permutation Coverage**: `Amort.Sorting.factorial_le_card_leaves`, `factorial_le_leafCount`, and `factorial_le_two_pow_depth` proving $n! \le \text{leafCount } T \le 2^{\text{depth } T}$.
- **Worst-Case Depth Bound**: `Amort.Sorting.clog_factorial_le_depth` establishing $\text{Nat.clog } 2\ (n!) \le \text{depth } T$.
- **Combinatorial Factorial Bound**: `Amort.Sorting.pow_div_two_le_factorial` proving $(n/2)^{n/2} \le n!$.
- **Asymptotics Bridge**:
  - `isBigO_n_log_n_factorial` proving $n \log n = O(\log(n!))$ ($\log(n!) = \Omega(n \log n)$).
  - `isTheta_factorial_n_log_n` proving $\log(n!) = \Theta(n \log n)$.
  - `isBigO_n_log_n_clog_factorial` and `isBigO_n_log_n_depth` proving $n \log n = O(\text{depth } T_n)$.
- **Documentation**: Suite overview in [`Amort/Sorting/Sorting.md`](Amort/Sorting/Sorting.md) and detailed proof strategy in [`Amort/Sorting/LowerBound.md`](Amort/Sorting/LowerBound.md).

### 7. Algorithmic Recurrence & Complexity Theorems
- **Compositional Complexity Algebra**: `Amort.Recurrence.Composition` formalizing nested loop products $O(g_1 \cdot g_2)$, sequential phase sums $O(g_1 + g_2)$, maximum phase bounds $O(\max(g_1, g_2))$, and phase dominance in Mathlib `IsBigO`. Documented in [`Amort/Recurrence/Composition.md`](Amort/Recurrence/Composition.md).
- **Linear & Telescoping Recurrences**: `Amort.Recurrence.Telescoping` with fundamental telescoping inequality, constant step bounds $O(n)$, power step bounds $O(n^{k+1})$, and connection to Insertion Sort comparison complexity ($O(n^2)$). Documented in [`Amort/Recurrence/Telescoping.md`](Amort/Recurrence/Telescoping.md).
- **Halving Recurrences & Binary Search**: `Amort.Recurrence.Halving` and `Amort.Recurrence.BinarySearch` with bit-length reduction $\text{size}(n/2) = \text{size } n - 1$, halving recurrence bounds $T(n) \le c \cdot \text{size } n + T(1)$, logarithmic bridge $\text{size } n = O(\log n)$, representative binary search step counter, and $O(\log n)$ complexity. Documented in [`Amort/Recurrence/HalvingAndBinarySearch.md`](Amort/Recurrence/HalvingAndBinarySearch.md).
- **Divide-and-Conquer Master Recurrence**: `Amort.Recurrence.MasterTheorem` formalizing balanced divide-and-conquer recurrences with integer rounding ($T(n) \le T(\lceil n/2 \rceil) + T(\lfloor n/2 \rfloor) + c \cdot n$), proving dyadic bounds $T(n) \le T(1) n + c n k$, $O(n \log n)$ asymptotics, and connecting to Merge Sort. Documented in [`Amort/Recurrence/MasterTheorem.md`](Amort/Recurrence/MasterTheorem.md).
- **State-Space Dynamic Programming**: `Amort.Recurrence.DP` formalizing general finite state-space DP complexity ($\text{totalCost} \le |S| \cdot C$), 2D grid DP specialization ($(n+1)(m+1)$ states), asymptotic product bridges, and application to LCS. Documented in [`Amort/Recurrence/DP.md`](Amort/Recurrence/DP.md).
- **Documentation**: Suite overview in [`Amort/Recurrence/Recurrence.md`](Amort/Recurrence/Recurrence.md).

### 8. Textbook String Algorithms (`Amort.String`)
- **Naive String Matching**: `Amort.String.NaiveMatch` formalizing sliding-window matching, character comparison counting, concrete upper bound $\le (n - m + 1) \cdot m \le n \cdot m$, and substring occurrence correctness. Documented in [`Amort/String/NaiveMatch.md`](Amort/String/NaiveMatch.md).
- **Knuth-Morris-Pratt (KMP)**: `Amort.String.KMP` formalizing failure function $\pi$ with preprocessing bound $\le 2m$, amortized potential function $\Phi(j) = j$ proving scanning bound $\le 2n$, combined linear bound $\le 2(n + m)$, and equivalence to naive matching. Documented in [`Amort/String/KMP.md`](Amort/String/KMP.md).
- **Longest Common Subsequence (LCS)**: `Amort.String.LCS` formalizing recursive formulation, constructive maximal common subsequence witness, bottom-up $(n + 1) \times (m + 1)$ dynamic programming table, and concrete operation bound $\le (n + 1) \cdot (m + 1)$ ($O(n \cdot m)$). Documented in [`Amort/String/LCS.md`](Amort/String/LCS.md).
- **Edit Distance (Levenshtein Distance)**: `Amort.String.EditDistance` formalizing recursive edit distance, explicit alignment operations and cost, minimal-cost alignment correctness proof, bottom-up $(n + 1) \times (m + 1)$ dynamic programming matrix, and concrete step bound $\le (n + 1) \cdot (m + 1)$ ($O(n \cdot m)$). Documented in [`Amort/String/EditDistance.md`](Amort/String/EditDistance.md).
- **Asymptotics & Composition Bridges**: `Amort.String.Asymptotics` connecting 2D table bounds to `Amort.Recurrence.Composition` (`isBigO_nested_loops_nat`), linear KMP bounds to `isBigO_sequential_add_nat`, and proving formal $O(n \cdot m)$ and $O(n + m)$ `IsBigO` bounds under `Filter.atTop` on $\mathbb{N} \times \mathbb{N}$.
- **Documentation**: Suite overview in [`Amort/String/String.md`](Amort/String/String.md).

### 9. Textbook Dynamic Programming Algorithms (`Amort.DP`)
- **Interval DP: Matrix Chain Multiplication**: `Amort.DP.MatrixChain` formalizing matrix dimensions, Bellman recurrence, interval state space `IntervalState n` with exact cardinality $n(n+1)/2 \le n^2$, and $O(n^3)$ operational bound via `Amort.Recurrence.DP`. Documented in [`Amort/DP/MatrixChain.md`](Amort/DP/MatrixChain.md).
- **Grid DP: 0/1 Knapsack**: `Amort.DP.Knapsack` formalizing item weights and values, capacity $W$, Bellman recurrence, mathematical correctness against subcollections (soundness, completeness, optimality), and $O(n \cdot W)$ bound via `Amort.Recurrence.GridDP`. Documented in [`Amort/DP/Knapsack.md`](Amort/DP/Knapsack.md).
- **Predecessor State-Space DP: Longest Increasing Subsequence**: `Amort.DP.LIS` formalizing strictly increasing sublists, prefix/recursive formulations, mathematical correctness (soundness and completeness), and $O(n^2)$ state-space model on $\text{Fin } n$ examining predecessors $j < i$ with triangular bound $n(n-1)/2$. Documented in [`Amort/DP/LIS.md`](Amort/DP/LIS.md).
- **Asymptotic Complexity Bridges**: `Amort.DP.Asymptotics` connecting Matrix Chain ($O(n^3)$), 0/1 Knapsack ($O(n \cdot W)$), and LIS ($O(n^2)$) to Mathlib's `Mathlib.Analysis.Asymptotics.IsBigO` under `Filter.atTop`.
- **Documentation**: Suite overview and comparison in [`Amort/DP/DP.md`](Amort/DP/DP.md).

### 10. Textbook Graph Algorithms (`Amort.Graph`)
- **Floyd-Warshall Shortest Paths**: `Amort.Graph.FloydWarshall` formalizing all-pairs shortest paths via 3D dynamic programming on `Fin (n + 1) × Fin n × Fin n` with exact cardinality $(n + 1) \cdot n^2$, and $O(n^3)$ operational bound via `Amort.Recurrence.DP`. Documented in [`Amort/Graph/FloydWarshall.md`](Amort/Graph/FloydWarshall.md).
- **Bellman-Ford Shortest Paths**: `Amort.Graph.BellmanFord` formalizing single-source shortest paths via $(n - 1)$ edge relaxation passes, proving $(n - 1) \cdot |E| \le n \cdot |E|$ step bound and $O(|V| \cdot |E|)$ complexity via `Amort.Recurrence.Composition.isBigO_nested_loops_nat`. Documented in [`Amort/Graph/BellmanFord.md`](Amort/Graph/BellmanFord.md).
- **Linear Graph Traversals & Handshaking**: `Amort.Graph.Traversal` formalizing adjacency list representations, the directed Handshaking Lemma $\sum_{v} \text{outdeg}(v) = |E|$, queue-based BFS operational bound $\le |V| + |E|$, and unweighted shortest-path distance correctness. Documented in [`Amort/Graph/Traversal.md`](Amort/Graph/Traversal.md).
- **Topological Sort**: `Amort.Graph.TopologicalSort` formalizing Kahn's in-degree zero queue algorithm, proving $\le |V| + |E|$ step bound and topological ordering correctness guaranteeing DAG cycle-freedom. Documented in [`Amort/Graph/TopologicalSort.md`](Amort/Graph/TopologicalSort.md).
- **Disjoint Set Union (Union-Find)**: `Amort.Graph.DSU` formalizing union-by-rank, the exponential subtree size invariant $2^{\text{rank}} \le n$, logarithmic tree depth and find step bounds $\le \text{Nat.size } n \le \log_2 n$, and proving $m$ operations on $n$ elements execute in $\le 3(n + m) \cdot \text{Nat.size } n$ ($O((n + m) \log n)$). Documented in [`Amort/Graph/DSU.md`](Amort/Graph/DSU.md).
- **Kruskal's Minimum Spanning Tree**: `Amort.Graph.Kruskal` formalizing edge sorting connecting to `Amort.Sorting.MergeSort`, DSU cycle checking, $O(|E| \log |V|)$ overall time complexity, and greedy Cut-Property optimality. Documented in [`Amort/Graph/Kruskal.md`](Amort/Graph/Kruskal.md).
- **Asymptotic Complexity Bridges**: `Amort.Graph.Asymptotics` connecting Floyd-Warshall ($O(n^3)$), Bellman-Ford ($O(|V| \cdot |E|)$), BFS ($O(|V| + |E|)$), Topological Sort ($O(|V| + |E|)$), DSU ($O((n + m) \log n)$), and Kruskal ($O(|E| \log |V|)$) to Mathlib's `Mathlib.Analysis.Asymptotics.IsBigO` under `Filter.atTop`.
- **Documentation**: Suite overview and comparison in [`Amort/Graph/Graph.md`](Amort/Graph/Graph.md).

## Building and Verification

```bash
lake build
```

Full build executes with 0 warnings and 0 errors across 2014 jobs. All theorems rely exclusively on standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`) with 0 `sorryAx`.

## Disclaimer

This is a personal side project. The views, opinions, and formalizations expressed here are solely those of the author and do not represent or reflect the views, positions, or endorsements of the author's employer (Google LLC). Any rights or intellectual property may be subject to employer agreements, but this project is not an official Google product.
