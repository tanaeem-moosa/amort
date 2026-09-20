# amort

AI-assisted formalization of time complexity and correctness of algorithms in Lean 4.

## Modules Overview

This repository formalizes algorithms and their computational complexity in `Amort/GCD/`,
`Amort/Sorting/`, `Amort/Recurrence/`, `Amort/String/`, `Amort/DP/`, `Amort/Graph/`,
`Amort/DataStructure/`, `Amort/Greedy/`, `Amort/Geometry/`, `Amort/NumberTheory/`, `Amort/Algebraic/`,
`Amort/Complexity/`, `Amort/Approximation/`, `Amort/Randomized/`, `Amort/LP/`, and
`Amort/Distributed/`:

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
- **Prefix Trie (Prefix Tree Dictionary)**: `Amort.String.Trie` formalizing prefix trie representation with explicit root, child transitions, word termination markers, prefix retrieval soundness, and $O(\sum |P_i|)$ dictionary construction. Documented in [`Amort/String/Trie.md`](Amort/String/Trie.md).
- **Aho-Corasick Multi-Pattern Matching Automaton**: `Amort.String.AhoCorasick` formalizing failure links (suffix links), depth contraction invariant, tree-depth potential function $\Phi(u) = \text{depth}(u)$ proving linear text scanning $\le 2|T|$, and overall search complexity $O(\sum |P_i| + |T| + z)$. Documented in [`Amort/String/AhoCorasick.md`](Amort/String/AhoCorasick.md).
- **Gusfield's Z-Algorithm**: `Amort.String.ZAlgorithm` formalizing the $Z$-array $Z[i] = \text{LCP}(S, S[i..])$, rightmost match window $[l, r]$, two-case branch logic, window expansion progress invariant proving linear comparison bound $\le 2|S|$, and pattern matching reduction $Z(P \$ T)$. Documented in [`Amort/String/ZAlgorithm.md`](Amort/String/ZAlgorithm.md).
- **Rabin-Karp Rolling Hash Matching**: `Amort.String.RabinKarp` formalizing polynomial rolling hash modulo prime $p$, $O(1)$ sliding window hash update identity, hash congruence soundness, and average-case $O(|T| + |P|)$ search complexity. Documented in [`Amort/String/RabinKarp.md`](Amort/String/RabinKarp.md).
- **Suffix Array & Kasai's Linear LCP**: `Amort.String.SuffixArray` formalizing suffix orderings, inverse permutation ranks, Kasai's height decrement invariant $h_{i+1} \ge h_i - 1$, and telescoping summation theorem bounding comparison increments by $2n$ ($O(n)$). Documented in [`Amort/String/SuffixArray.md`](Amort/String/SuffixArray.md).
- **Asymptotics & Composition Bridges**: `Amort.String.Asymptotics` connecting 2D table bounds to `Amort.Recurrence.Composition` (`isBigO_nested_loops_nat`), linear KMP bounds to `isBigO_sequential_add_nat`, and proving formal $O(n \cdot m)$ and $O(n + m)$ `IsBigO` bounds under `Filter.atTop` on $\mathbb{N} \times \mathbb{N}$.
- **Advanced Asymptotics Bridges**: `Amort.String.AdvancedAsymptotics` connecting Trie construction ($O(\sum |P_i|)$), Aho-Corasick search ($O(\sum |P_i| + |T| + z)$), Z-Algorithm ($O(|S|)$), Rabin-Karp ($O(|T| + |P|)$), and Kasai ($O(n)$) to Mathlib's `Mathlib.Analysis.Asymptotics.IsBigO` under `Filter.atTop`. Documented in [`Amort/String/AdvancedAsymptotics.md`](Amort/String/AdvancedAsymptotics.md).
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
- **Dijkstra's Shortest Paths**: `Amort.Graph.Dijkstra` formalizing single-source shortest paths for non-negative edge weights using a priority queue, proving the greedy choice invariant, and bounding operations by $(|V| + |E|) \cdot \text{Nat.size } |V|$ ($O((|V| + |E|) \log |V|)$). Documented in [`Amort/Graph/Dijkstra.md`](Amort/Graph/Dijkstra.md).
- **Network Flow & Max-Flow Min-Cut Theorem**: `Amort.Graph.MaxFlow` formalizing flow networks, capacity constraints, conservation, the Cut-Flow Identity, Weak Duality, the Max-Flow Min-Cut Theorem on tight residual cuts, and Edmonds-Karp complexity $O(|V| \cdot |E|^2)$. Documented in [`Amort/Graph/MaxFlow.md`](Amort/Graph/MaxFlow.md).
- **Strongly Connected Components (SCC)**: `Amort.Graph.SCC` formalizing directed reachability, mutual reachability equivalence classes, component soundness and completeness, acyclicity of the condensation DAG, and Kosaraju's two-pass DFS algorithm ($O(|V| + |E|)$). Documented in [`Amort/Graph/SCC.md`](Amort/Graph/SCC.md).
- **Eulerian Circuits & Hierholzer's Algorithm**: `Amort.Graph.Eulerian` formalizing the in-degree Handshaking equality, degree balance conditions, trail continuity, Hierholzer's cycle splicing algorithm, and linear operational bound $O(|V| + |E|)$. Documented in [`Amort/Graph/Eulerian.md`](Amort/Graph/Eulerian.md).
- **Linear Graph Traversals & Handshaking**: `Amort.Graph.Traversal` formalizing adjacency list representations, the directed Handshaking Lemma $\sum_{v} \text{outdeg}(v) = |E|$, queue-based BFS operational bound $\le |V| + |E|$, and unweighted shortest-path distance correctness. Documented in [`Amort/Graph/Traversal.md`](Amort/Graph/Traversal.md).
- **Topological Sort**: `Amort.Graph.TopologicalSort` formalizing Kahn's in-degree zero queue algorithm, proving $\le |V| + |E|$ step bound and topological ordering correctness guaranteeing DAG cycle-freedom. Documented in [`Amort/Graph/TopologicalSort.md`](Amort/Graph/TopologicalSort.md).
- **Disjoint Set Union (Union-Find)**: `Amort.Graph.DSU` formalizing union-by-rank, the exponential subtree size invariant $2^{\text{rank}} \le n$, logarithmic tree depth and find step bounds $\le \text{Nat.size } n \le \log_2 n$, and proving $m$ operations on $n$ elements execute in $\le 3(n + m) \cdot \text{Nat.size } n$ ($O((n + m) \log n)$). Documented in [`Amort/Graph/DSU.md`](Amort/Graph/DSU.md).
- **Kruskal's Minimum Spanning Tree**: `Amort.Graph.Kruskal` formalizing edge sorting connecting to `Amort.Sorting.MergeSort`, DSU cycle checking, $O(|E| \log |V|)$ overall time complexity, and greedy Cut-Property optimality. Documented in [`Amort/Graph/Kruskal.md`](Amort/Graph/Kruskal.md).
- **Prim's Minimum Spanning Tree**: `Amort.Graph.Prim` formalizing priority queue frontier selection, Cut-Property greedy optimality, operational bound $(|V| + |E|) \cdot \text{Nat.size } |V|$ ($O(|E| \log |V|)$ on connected graphs), and algorithmic contrast with Kruskal. Documented in [`Amort/Graph/Prim.md`](Amort/Graph/Prim.md).
- **Asymptotic Complexity Bridges**: `Amort.Graph.Asymptotics` and `Amort.Graph.AdvancedAsymptotics` connecting Floyd-Warshall ($O(n^3)$), Bellman-Ford ($O(|V| \cdot |E|)$), BFS ($O(|V| + |E|)$), Topological Sort ($O(|V| + |E|)$), DSU ($O((n + m) \log n)$), Kruskal ($O(|E| \log |V|)$), Dijkstra ($O((|V| + |E|) \log |V|)$), Edmonds-Karp ($O(|V| \cdot |E|^2)$), Kosaraju ($O(|V| + |E|)$), Hierholzer ($O(|V| + |E|)$), and Prim ($O(|E| \log |V|)$) to Mathlib's `Mathlib.Analysis.Asymptotics.IsBigO` under `Filter.atTop`. Documented in [`Amort/Graph/AdvancedAsymptotics.md`](Amort/Graph/AdvancedAsymptotics.md).
- **Documentation**: Suite overview and comparison in [`Amort/Graph/Graph.md`](Amort/Graph/Graph.md).

### 11. Textbook Data Structures & Online Query Algorithms (`Amort.DataStructure`)
- **Binary Heaps & Heapsort**: `Amort.DataStructure.BinaryHeap` formalizing binary heap order invariants, root minimality, logarithmic height, sift-up/down bounds $\le \text{Nat.size } n$, linear build-heap theorem $\sum_{h=0}^{\log n} (n / 2^h) h \le 2n$ via geometric sum, and heapsort comparison complexity bounded by $4n \log n + 2$. Documented in [`Amort/DataStructure/BinaryHeap.md`](Amort/DataStructure/BinaryHeap.md).
- **Online Running Median with Dual Heaps**: `Amort.DataStructure.OnlineMedian` formalizing dual-heap streaming model (max-heap `low` + min-heap `high`), balance condition $|size(low) - size(high)| \le 1$, partition condition $\max(low) \le \min(high)$, mathematical median soundness proving $\max(low)$ is the true median, $O(1)$ query time, and $O(\log n)$ insertion/rebalancing work. Documented in [`Amort/DataStructure/OnlineMedian.md`](Amort/DataStructure/OnlineMedian.md).
- **Balanced Binary Search Trees**: `Amort.DataStructure.BalancedBST` formalizing height-balanced BSTs with size annotations, $O(1)$ tree rotations preserving BST ordering and size annotations, and $O(\log n)$ online order-statistic queries (`rank`, `select`, `find`, `insert`). Documented in [`Amort/DataStructure/BalancedBST.md`](Amort/DataStructure/BalancedBST.md).
- **Dynamic Array Capacity Doubling**: `Amort.DataStructure.DynamicArray` formalizing capacity doubling, potential function $\Phi = 2n - C$, amortized push $\hat{c} \le 3$, non-negativity $\Phi \ge 0$, and multi-operation telescoping bound $\sum c_i \le 3k + \Phi_0$. Documented in [`Amort/DataStructure/DynamicArray.md`](Amort/DataStructure/DynamicArray.md).
- **Two-Stack FIFO Queue**: `Amort.DataStructure.TwoStackQueue` formalizing two-stack FIFO queue, potential function $\Phi = 2 \cdot |\text{inStack}|$, amortized push $\hat{c} = 3$, amortized pop $\hat{c} \le 1$, FIFO sequence append soundness, and multi-operation telescoping bound $\sum c_i \le 3m$. Documented in [`Amort/DataStructure/TwoStackQueue.md`](Amort/DataStructure/TwoStackQueue.md).
- **Asymptotic Complexity Bridges**: `Amort.DataStructure.Asymptotics` connecting linear build-heap ($O(n)$), heapsort ($O(n \log n)$), online median query ($O(1)$) and insert ($O(\log n)$), balanced BST queries ($O(\log n)$), dynamic array pushes ($O(k)$), and two-stack queue operations ($O(m)$) to Mathlib's `Mathlib.Analysis.Asymptotics.IsBigO` under `Filter.atTop`.
- **Documentation**: Suite overview and comparison in [`Amort/DataStructure/DataStructure.md`](Amort/DataStructure/DataStructure.md).

### 12. Greedy Algorithms & Linear Selection (`Amort.Greedy`)
- **Interval Scheduling / Activity Selection**: `Amort.Greedy.IntervalScheduling` formalizing compatible intervals $start < finish$, greedy earliest-finish-time selection, exchange argument optimality theorem, and $O(n \log n)$ operational step bound. Documented in [`Amort/Greedy/IntervalScheduling.md`](Amort/Greedy/IntervalScheduling.md).
- **Huffman Coding & Optimal Prefix Trees**: `Amort.Greedy.Huffman` formalizing weighted symbol alphabets, binary prefix trees, equivalence between external path length and internal node weights, greedy choice property for minimal-weight siblings at maximum depth, and $O(n \log n)$ priority queue construction bound. Documented in [`Amort/Greedy/Huffman.md`](Amort/Greedy/Huffman.md).
- **Median-of-Medians Deterministic Selection (BFPRT)**: `Amort.Greedy.MedianOfMedians` formalizing group-of-5 partitioning, group medians, median-of-medians pivot quality theorem guaranteeing $\ge 3n/10 - 6$ elements bounded by the pivot, recursive branch bound $\le 7n/10 + 6$, and linear-time recurrence $T(n) \le T(\lceil n/5 \rceil) + T(7n/10 + 6) + c \cdot n \implies O(n)$. Documented in [`Amort/Greedy/MedianOfMedians.md`](Amort/Greedy/MedianOfMedians.md).
- **Asymptotic Complexity Bridges**: `Amort.Greedy.Asymptotics` connecting Interval Scheduling ($O(n \log n)$), Huffman Coding ($O(n \log n)$), and Median-of-Medians ($O(n)$) to Mathlib's `Mathlib.Analysis.Asymptotics.IsBigO` under `Filter.atTop`. Documented in [`Amort/Greedy/Asymptotics.md`](Amort/Greedy/Asymptotics.md).
- **Documentation**: Suite overview in [`Amort/Greedy/Greedy.md`](Amort/Greedy/Greedy.md).

### 13. Computational Geometry (`Amort.Geometry`)
- **2D Convex Hull (Graham Scan / Monotone Chain)**: `Amort.Geometry.ConvexHull` formalizing 2D points `Point2D`, orientation test via 2D determinant cross product, monotone chain stack hull construction, potential function amortized scanning bound $\le 2n$ stack operations, and $O(n \log n)$ total complexity dominated by sorting. Documented in [`Amort/Geometry/ConvexHull.md`](Amort/Geometry/ConvexHull.md).
- **Closest Pair of Points**: `Amort.Geometry.ClosestPair` formalizing squared Euclidean distance, divide-and-conquer splitting by median $x$-coordinate, strip geometric sparsity / packing lemma bounding any $\delta \times \delta$ square to $\le 4$ points and strip neighbors to $\le 7$, and divide-and-conquer recurrence $T(n) \le 2T(n/2) + c \cdot n \implies O(n \log n)$. Documented in [`Amort/Geometry/ClosestPair.md`](Amort/Geometry/ClosestPair.md).
- **Asymptotic Complexity Bridges**: `Amort.Geometry.Asymptotics` connecting 2D Convex Hull ($O(n \log n)$) and Closest Pair of Points ($O(n \log n)$) to Mathlib's `Mathlib.Analysis.Asymptotics.IsBigO` under `Filter.atTop`. Documented in [`Amort/Geometry/Asymptotics.md`](Amort/Geometry/Asymptotics.md).
- **Documentation**: Suite overview in [`Amort/Geometry/Geometry.md`](Amort/Geometry/Geometry.md).

### 14. Number Theoretic Algorithms (`Amort.NumberTheory`)
- **Fast Modular Exponentiation (Binary Exponentiation)**: `Amort.NumberTheory.ModExp` formalizing repeated squaring computing $a^b \bmod m$, loop state correctness invariant $acc \cdot base^{exp} \equiv a^b \pmod m$, and logarithmic multiplication step bound $\le 2 \cdot \text{Nat.size } b \implies O(\log b)$. Documented in [`Amort/NumberTheory/ModExp.md`](Amort/NumberTheory/ModExp.md).
- **Extended Euclidean Algorithm**: `Amort.NumberTheory.ExtendedGCD` formalizing extended Euclidean division computing Bézout coefficients $x, y \in \mathbb{Z}$ satisfying $a \cdot x + b \cdot y = \gcd(a, b)$, quotient step linear combination invariants, two-step remainder halving theorem $2 \cdot r_{k+2} < r_k$, and logarithmic step bound $\le 2 \cdot \text{Nat.size}(\min a\ b) + 1 \implies O(\log(\min a\ b))$. Documented in [`Amort/NumberTheory/ExtendedGCD.md`](Amort/NumberTheory/ExtendedGCD.md).
- **Sieve of Eratosthenes**: `Amort.NumberTheory.Sieve` formalizing composite marking array model over $[2, n]$, correctness theorem proving integer $k \in [2, n]$ remains unmarked iff $k$ is prime, and harmonic operational work bound $\sum_{p \le n} (n / p) \le n \sum_{k=1}^n (1 / k) \le n (1 + \ln n) = O(n \log n)$. Documented in [`Amort/NumberTheory/Sieve.md`](Amort/NumberTheory/Sieve.md).
- **Asymptotic Complexity Bridges**: `Amort.NumberTheory.Asymptotics` connecting ModExp ($O(\log b)$), Extended GCD ($O(\log(\min a\ b))$), and Sieve of Eratosthenes ($O(n \log n)$) to Mathlib's `Mathlib.Analysis.Asymptotics.IsBigO` under `Filter.atTop`. Documented in [`Amort/NumberTheory/Asymptotics.md`](Amort/NumberTheory/Asymptotics.md).
- **Documentation**: Suite overview in [`Amort/NumberTheory/NumberTheory.md`](Amort/NumberTheory/NumberTheory.md).
 
### 15. Fast Algebraic & Divide-and-Conquer Algorithms (`Amort.Algebraic`)
- **Fast Fourier Transform (FFT) & Polynomial Multiplication**: `Amort.Algebraic.FFT` formalizing roots of unity, cancellation lemma ($\omega_{dn}^{dk} = \omega_n^k$), halving lemma, negation lemma, Cooley-Tukey Radix-2 decomposition $A(x) = A_{even}(x^2) + x A_{odd}(x^2)$, butterfly operation correctness, divide-and-conquer recurrence $T(n) \le 2T(n/2) + c \cdot n$, and linear-logarithmic operational complexity $O(n \log n)$ contrasting with naive $O(n^2)$. Documented in [`Amort/Algebraic/FFT.md`](Amort/Algebraic/FFT.md).
- **Strassen's Sub-Cubic Matrix Multiplication**: `Amort.Algebraic.Strassen` formalizing $2 \times 2$ block matrices over arbitrary rings, Strassen's 7 auxiliary multiplications, algebraic equivalence theorem $C_{ij} = (A \cdot B)_{ij}$, divide-and-conquer recurrence $T(n) \le 7T(n/2) + c \cdot n^2$, and sub-cubic operational bound $O(n^{\log_2 7})$ ($O(n^{2.807})$). Documented in [`Amort/Algebraic/Strassen.md`](Amort/Algebraic/Strassen.md).
- **Asymptotic Complexity Bridges**: `Amort.Algebraic.Asymptotics` connecting FFT ($O(n \log n)$), polynomial multiplication ($O(n \log n)$), and Strassen's algorithm ($O(n^{\log_2 7})$) to Mathlib's `Mathlib.Analysis.Asymptotics.IsBigO` under `Filter.atTop`, with rigorous proof that $\log_2 7 < 3$. Documented in [`Amort/Algebraic/Algebraic.md`](Amort/Algebraic/Algebraic.md).
- **Documentation**: Suite overview in [`Amort/Algebraic/Algebraic.md`](Amort/Algebraic/Algebraic.md).
 
### 16. NP-Completeness, Complexity Classes & Classical Reductions (`Amort.Complexity`)
- **Complexity Classes P and NP & Polynomial Verifiers**: `Amort.Complexity.Classes` formalizing languages over alphabets, canonical polynomial bounds `polyEval c k n`, deterministic deciders (Class P), polynomial-time verifiers and certificate relations (Class NP) proving constructive embedding $P \subseteq NP$, polynomial-time many-one reductions ($A \le_P B$) with reflexivity and transitivity, preservation of P under reductions, and NP-completeness. Documented in [`Amort/Complexity/Classes.md`](Amort/Complexity/Classes.md).
- **2-SAT Linear-Time Solver via SCC**: `Amort.Complexity.TwoSAT` formalizing 2-CNF boolean logic, implication digraph ($\neg u \to v$ and $\neg v \to u$), contrapositive symmetry, connection to `Amort.Graph.SCC`, soundness and completeness theorem proving a 2-CNF formula is satisfiable iff no variable $x$ lies in the same SCC as $\neg x$, and $O(|V| + |E|) = O(n + m)$ linear operational step bound. Documented in [`Amort/Complexity/TwoSAT.md`](Amort/Complexity/TwoSAT.md).
- **Karp's Foundational Reductions & Complement Duality**: `Amort.Complexity.KarpReductions` formalizing simple graphs, Independent Set, Vertex Cover, Clique, the Complement Duality Theorem ($S \text{ IS in } G \iff V \setminus S \text{ VC in } G \iff S \text{ Clique in } \overline{G}$), 3-SAT to Independent Set clause triangle gadget reduction soundness and completeness, and the reduction chain $\text{3-SAT} \le_P \text{Independent Set} \le_P \text{Vertex Cover} \le_P \text{Clique}$. Documented in [`Amort/Complexity/KarpReductions.md`](Amort/Complexity/KarpReductions.md).
- **Asymptotic Complexity Bridges**: `Amort.Complexity.Asymptotics` connecting 2-SAT linear time ($O(n + m)$), canonical polynomial growth, 3-SAT gadget graph size ($O(m)$ vertices, $O(m^2)$ edges), and complement graph edge complexity ($O(n^2)$) to Mathlib's `Mathlib.Analysis.Asymptotics.IsBigO` under `Filter.atTop`. Documented in [`Amort/Complexity/Complexity.md`](Amort/Complexity/Complexity.md).
- **Documentation**: Suite overview in [`Amort/Complexity/Complexity.md`](Amort/Complexity/Complexity.md).

### 17. Approximation Algorithms (`Amort.Approximation`)
- **Vertex Cover 2-Approximation**: `Amort.Approximation.VertexCover` formalizing greedy maximal
  matching edge selection, lower bound proving any vertex cover must select at least one endpoint
  from each matching edge ($|M| \le |C^*|$), approximation ratio $|C| = 2|M| \le 2 \cdot |C^*|$,
  and linear operational complexity $O(|V| + |E|)$.
  Documented in [`Amort/Approximation/VertexCover.md`](Amort/Approximation/VertexCover.md).
- **Metric TSP 2-Approximation**: `Amort.Approximation.MetricTSP` formalizing complete graphs with
  metric triangle inequality $d(u, w) \le d(u, v) + d(v, w)$, MST weight lower bound
  $\text{weight}(\text{MST}) \le \text{OPT}_{\text{TSP}}$, double-tree Eulerian tour,
  shortcutting theorem, and bound $\text{cost}(\text{Tour}) \le 2 \cdot \text{OPT}_{\text{TSP}}$.
  Documented in [`Amort/Approximation/MetricTSP.md`](Amort/Approximation/MetricTSP.md).
- **Set Cover Greedy $H(n)$-Approximation**: `Amort.Approximation.SetCover` formalizing set systems,
  greedy maximum marginal coverage selection, harmonic potential charging scheme, and harmonic
  potential bound $|\mathcal{C}_{\text{greedy}}| \le H(n) \cdot \text{OPT}$.
  Documented in [`Amort/Approximation/SetCover.md`](Amort/Approximation/SetCover.md).
- **Asymptotic Complexity Bridges**: `Amort.Approximation.Asymptotics` connecting Vertex Cover
  ($O(|V| + |E|)$), Metric TSP ($O(n^2 \log n)$), and Set Cover ($O(m \cdot n)$) to Mathlib's
  `Mathlib.Analysis.Asymptotics.IsBigO` under `Filter.atTop`.
- **Documentation**: Overview in
  [`Amort/Approximation/Approximation.md`](Amort/Approximation/Approximation.md).

### 18. Advanced Graph Algorithms & Bipartite Matching (`Amort.Graph.Advanced`)
- **Hopcroft-Karp Maximum Bipartite Matching**: `Amort.Graph.Advanced.HopcroftKarp` formalizing
  bipartite graphs, matchings, alternating paths, augmenting paths, layered BFS phase, maximal DFS
  augmenting phase, strictly increasing path lengths across phases ($d_{i+1} \ge d_i + 2$),
  phase bound $\le 2\sqrt{|V|}$, and $O(|E|\sqrt{|V|})$ worst-case time complexity.
  Documented in [`Amort/Graph/Advanced/HopcroftKarp.md`](Amort/Graph/Advanced/HopcroftKarp.md).
- **Hall's Marriage Theorem**: `Amort.Graph.Advanced.HallMarriage` formalizing bipartite graph
  $G = (L, R, E)$, neighborhood $N(S)$ for subsets $S \subseteq L$, combinatorial condition
  $|N(S)| \ge |S|$, max-flow reduction, and equivalence with saturating matchings.
  Documented in [`Amort/Graph/Advanced/HallMarriage.md`](Amort/Graph/Advanced/HallMarriage.md).
- **Bridges & Articulation Points (Tarjan's DFS)**: `Amort.Graph.Advanced.BridgeTarjan` formalizing
  DFS discovery order $\text{disc}[u]$, low-link values $\text{low}[u]$, bridge characterization
  $\text{low}[v] > \text{disc}[u]$, articulation point characterization, and $O(|V| + |E|)$ bound.
  Documented in [`Amort/Graph/Advanced/BridgeTarjan.md`](Amort/Graph/Advanced/BridgeTarjan.md).
- **Asymptotic Complexity Bridges**: `Amort.Graph.Advanced.Asymptotics` connecting Hopcroft-Karp
  ($O(|E|\sqrt{|V|})$) and Tarjan bridge-finding ($O(|V| + |E|)$) to Mathlib's
  `Mathlib.Analysis.Asymptotics.IsBigO` under `Filter.atTop`.
- **Documentation**: Overview in
  [`Amort/Graph/Advanced/AdvancedGraph.md`](Amort/Graph/Advanced/AdvancedGraph.md).

### 19. Randomized Algorithms & Probabilistic Complexity (`Amort.Randomized`)
- **Expected Complexity of Randomized Quicksort**: `Amort.Randomized.Quicksort` formalizing
  comparison
  indicators $X_{ij}$ for sorted elements $z_i, z_j$, pivot probability lemma
  $\mathbb{P}[X_{ij} = 1] = \frac{2}{j - i + 1}$, linearity of expectation, and harmonic bound
  $\mathbb{E}[C] = \sum_{k=1}^{n-1} \frac{2(n-k)}{k+1} \le 2n H(n) = O(n \log n)$.
  Documented in [`Amort/Randomized/Quicksort.md`](Amort/Randomized/Quicksort.md).
- **Karger's Min-Cut Contraction Algorithm**: `Amort.Randomized.KargerMinCut` formalizing multigraph
  contraction, degree/edge bounds ($k \le \text{deg}(v) \implies |E| \ge n k / 2$),
  single contraction survival probability $\ge (n-2)/n$, telescoping success lower bound
  $\mathbb{P}[\text{success}] \ge \prod_{i=0}^{n-3} (1 - \frac{2}{n - i}) = \frac{2}{n(n-1)}$,
  and repetition amplification to $1 - \delta$.
  Documented in [`Amort/Randomized/KargerMinCut.md`](Amort/Randomized/KargerMinCut.md).
- **Universal Hashing & Reservoir Sampling**: `Amort.Randomized.UniversalHash` formalizing
  2-Universal
  hash families, collision probability bound $\forall x \ne y, \mathbb{P}[h(x) = h(y)] \le 1/m$,
  expected collision bound $\le n/m$ ($O(1)$ expected lookup), reservoir sampling algorithm, and
  streaming uniform invariant $\frac{k}{t} \cdot \frac{t}{t+1} = \frac{k}{t+1}$.
  Documented in [`Amort/Randomized/UniversalHash.md`](Amort/Randomized/UniversalHash.md).
- **Asymptotic Complexity Bridges**: `Amort.Randomized.Asymptotics` connecting Quicksort
  ($O(n \log n)$), Karger Min-Cut ($O(n^4)$), and Universal Hashing ($O(1)$) to Mathlib's
  `Mathlib.Analysis.Asymptotics.IsBigO` under `Filter.atTop`.
- **Documentation**: Overview in [`Amort/Randomized/Randomized.md`](Amort/Randomized/Randomized.md).

### 20. Linear Programming & Duality (`Amort.LP`)
- **Primal and Dual Formulations**: `Amort.LP.Duality` formalizing linear programs in standard inequality form over vectors ($Ax \le b, x \ge 0$ and $A^T y \ge c, y \ge 0$), with feasibility predicates `PrimalFeasible` and `DualFeasible`. Documented in [`Amort/LP/Duality.md`](Amort/LP/Duality.md).
- **Weak Duality & Optimality Certificates**: Formal proofs of `weak_duality` ($c^T x \le b^T y$), `optimality_certificate` ($c^T x^* = b^T y^* \implies \text{OPT}$), and unboundedness infeasibility corollaries (`dual_infeasible_of_unbounded_primal`, `primal_infeasible_of_unbounded_dual`).
- **Simplex Slack Form & Dictionary Invariant**: `Amort.LP.Simplex` formalizing dictionary representations $x_B = \bar{b} - \bar{A} x_N$, basic solution feasibility invariant $\bar{b} \ge 0$, ratio test bounds, invariant preservation under pivoting (`pivot_preserves_feasibility`, `new_b_bar_nonneg`), and objective progression (`obj_increases_of_pivot`). Documented in [`Amort/LP/Simplex.md`](Amort/LP/Simplex.md).
- **Asymptotic Complexity Bridges**: `Amort.LP.Asymptotics` connecting simplex pivot step ($O(m \cdot n)$) and feasibility checking to Mathlib `IsBigO` under `Filter.atTop` on $\mathbb{N} \times \mathbb{N}$. Documented in [`Amort/LP/Asymptotics.md`](Amort/LP/Asymptotics.md).
- **Documentation**: Suite overview in [`Amort/LP/LP.md`](Amort/LP/LP.md).

### 21. Tarjan's Inverse Ackermann Bound for DSU (`Amort.Graph.Ackermann`)
- **Ackermann Hierarchy & Functional Inverse**: `Amort.Graph.Ackermann.AckermannHierarchy` formalizing two-variable Ackermann function $A_k(n)$, strict monotonicity, exact milestone evaluations ($A(0, 1) = 2, A(1, 1) = 3, A(2, 1) = 5, A(3, 1) = 13, A(4, 1) = 65533$), functional inverse $\alpha(n) = \min \{ k \mid A(k, 1) \ge n \}$, and slow growth theorem ($\alpha(n) \le 4$ for all $n \le 65533$). Documented in [`Amort/Graph/Ackermann/AckermannHierarchy.md`](Amort/Graph/Ackermann/AckermannHierarchy.md).
- **Path Compression with Union-by-Rank**: `Amort.Graph.Ackermann.PathCompression` formalizing DSU with path compression during `find`, proving strict parent rank hierarchy invariant preservation (`compress_preserves_hierarchy`), and logarithmic rank bounds $\text{rank}(v) \le \log_2 n \le \text{Nat.size } n$. Documented in [`Amort/Graph/Ackermann/PathCompression.md`](Amort/Graph/Ackermann/PathCompression.md).
- **Potential Function Analysis & Amortized Bound**: `Amort.Graph.Ackermann.PotentialBound` formalizing rank level intervals $[A_k(r), A_{k+1}(r)]$, potential function $\Phi(v)$, amortized telescoping summation theorem (`amortized_telescoping_sum`), and total work bound $\text{dsuAckermannWork}(m, n) \le 6(m + n)(\alpha(n) + 1)$ ($O(m \cdot \alpha(n))$ for $m \ge n$). Documented in [`Amort/Graph/Ackermann/PotentialBound.md`](Amort/Graph/Ackermann/PotentialBound.md).
- **Asymptotic Complexity Bridges**: `Amort.Graph.Ackermann.Asymptotics` connecting DSU total work with path compression to Mathlib `IsBigO` under `Filter.atTop` on $\mathbb{N} \times \mathbb{N}$. Documented in [`Amort/Graph/Ackermann/Asymptotics.md`](Amort/Graph/Ackermann/Asymptotics.md).
- **Documentation**: Suite overview in [`Amort/Graph/Ackermann/Ackermann.md`](Amort/Graph/Ackermann/Ackermann.md).

### 22. Suffix Trees & Ukkonen's Online Linear-Time Construction (`Amort.String.SuffixTree`)
- **Compact Suffix Tree Structure**: `Amort.String.SuffixTree.CompactTree` formalizing slice intervals $[l, r]$ into string $S$, internal branching degree $\ge 2$, leaf count $\le n$, internal node bound $\le n - 1$ via tree combinatorics, and total node bound $\le 2n$. Documented in [`Amort/String/SuffixTree/CompactTree.md`](Amort/String/SuffixTree/CompactTree.md).
- **Suffix Links & Depth Invariants**: `Amort.String.SuffixTree.SuffixLink` formalizing suffix links mapping $a \beta$ to $\beta$, strict depth decrement invariant $\text{stringDepth}(\text{link}(u)) = \text{stringDepth}(u) - 1$, and link chain depth reduction $\text{stringDepth}(u) - k$. Documented in [`Amort/String/SuffixTree/SuffixLink.md`](Amort/String/SuffixTree/SuffixLink.md).
- **Ukkonen's Online Algorithm & $O(n)$ Bound**: `Amort.String.SuffixTree.Ukkonen` formalizing active point `(active_node, active_edge, active_len)`, the three extension rules (Rule 1, Rule 2, Rule 3), global end pointer $O(1)$ amortized leaf extensions, total Rule 2 splits $\le n$, total link traversals $\le 2n$, and linear time bound $\text{ukkonenWork}(n) \le 4n = O(n)$. Documented in [`Amort/String/SuffixTree/Ukkonen.md`](Amort/String/SuffixTree/Ukkonen.md).
- **Asymptotic Complexity Bridges**: `Amort.String.SuffixTree.Asymptotics` connecting Ukkonen operational work to Mathlib `IsBigO` under `Filter.atTop` on $\mathbb{N}$. Documented in [`Amort/String/SuffixTree/Asymptotics.md`](Amort/String/SuffixTree/Asymptotics.md).
- **Documentation**: Suite overview in [`Amort/String/SuffixTree/SuffixTree.md`](Amort/String/SuffixTree/SuffixTree.md).

### 23. Disjoint Set Union with Path Compression Only (`Amort.Graph.PathCompressionOnly`)
- **Minimal State & Arbitrary Linking**: `Amort.Graph.DSUPCO` containing parent pointers only
  (`parent : Fin n → Fin n`) without rank or size arrays, with arbitrary linking `unite(u, v)`.
- **Iterative Two-Pass Path Compression**: `findPath`, `findRoot`, and `compressPath` re-pointing
  all traversed nodes directly to root, proving post-condition `path_depth_one_after_find`.
- **Worst-Case Operations & Asymptotic Bounds**:
  - `linearChain_depth_zero`: linear chain has depth $n - 1$ ($\Omega(n)$ depth).
  - `isBigO_adversarialPCOWork_omega`: adversarial sequence requires $\Omega(n \log n)$ steps.
  - `isBigO_dsuPCOWork_atTop`: $m$ operations on $n$ elements bounded by $O((n + m) \log n)$.
- **Documentation**: Detailed architecture and invariant proofs in
  [`Amort/Graph/PathCompressionOnly.md`](Amort/Graph/PathCompressionOnly.md).

### 24. Quicksort Algorithm Canon (`Amort.Sorting.Quicksort`)
- **Algorithmic Correctness**: 3-way partitioning (`partition3`), length-fueled recursion
  (`quicksortFuel`, `quicksort`), permutation equivalence (`quicksort_perm`), sortedness
  (`quicksort_sorted`, `quicksort_sortedLE`), and exact equivalence to Mathlib
  (`quicksort_eq_mergeSort`, `quicksort_eq_insertionSort`).
- **Worst-Case Quadratic Complexity**: `quicksortWorstCaseRec` step identity, exact closed-form
  solution $T(n) = n(n - 1) / 2$ (`quicksortWorstCaseRec_eq`), and tight $\Theta(n^2)$ asymptotics
  (`isTheta_quicksortWorstCase_sq`).
- **Deterministic Median (BFPRT) Worst-Case $O(n \log n)$**: Median-of-medians partition balance
  $\le \lfloor 7n/10 \rfloor + 3$ (`bfprt_partition_balance`), divide-and-conquer recurrence, and
  strictly worst-case $O(n \log n)$ asymptotics (`isBigO_bfprtQuicksort_n_log_n`).
- **Average-Case Expected $O(n \log n)$**: Expected recurrence $\mathbb{E}[T(n)]$, bridge to
  harmonic indicator bound in `Amort.Randomized.Quicksort` (`expected_quicksort_le_harmonic_bound`),
  and average-case $O(n \log n)$ asymptotics (`isBigO_quicksortAvg_n_log_n`).
- **Documentation**: Comprehensive architecture and proofs in
  [`Amort/Sorting/Quicksort.md`](Amort/Sorting/Quicksort.md).

### 25. Foundational Distributed Systems Canon (`Amort.Distributed`)
- **Causality & Logical Clocks**: `Amort.Distributed.Causality` formalizing distributed events,
  Lamport happens-before strict partial order, Lamport scalar clock consistency ($e_1 \to e_2
  \implies C(e_1) < C(e_2)$), and Vector Clock causal isomorphism ($V(e_1) < V(e_2) \iff e_1 \to
  e_2$). Documented in [`Amort/Distributed/Causality.md`](Amort/Distributed/Causality.md).
- **Impossibility Theorems**: `Amort.Distributed.Impossibility` formalizing the Gilbert-Lynch CAP
  Theorem (Linearizability and Availability cannot both hold across partitions) and Two Generals'
  impossibility of agreement over lossy channels by backward induction. Documented in
  [`Amort/Distributed/Impossibility.md`](Amort/Distributed/Impossibility.md).
- **Crash-Tolerant Consensus (Paxos & Raft)**: `Amort.Distributed.Consensus` formalizing majority
  quorum intersection ($Q_1 \cap Q_2 \ne \emptyset$), Single-Decree Paxos (Synod) Core Invariant,
  Learner Agreement ($v_1 = v_2$), Multi-Paxos Replicated Log safety, and Raft leader election
  and Log Matching invariants. Documented in
  [`Amort/Distributed/Consensus.md`](Amort/Distributed/Consensus.md).
- **Byzantine Fault Tolerance ($3f + 1$)**: `Amort.Distributed.BFT` formalizing PBFT quorum
  intersection ($2f + 1$ quorums intersect in $\ge f + 1$ nodes with $\ge 1$ honest),
  Lamport-Shostak-Pease $N \le 3f$ impossibility (3-node 1-traitor counterexample), and Oral
  Messages $OM(m)$ validity and agreement. Documented in
  [`Amort/Distributed/BFT.md`](Amort/Distributed/BFT.md).
- **Consistent Global Snapshots**: `Amort.Distributed.Snapshot` formalizing the Chandy-Lamport
  distributed snapshot algorithm with FIFO marker-passing rules, proving the recorded state
  forms a consistent cut ($r \le T_q \implies s \le T_p$) and channel state recording soundness.
  Documented in [`Amort/Distributed/Snapshot.md`](Amort/Distributed/Snapshot.md).
- **Suite Documentation**: Master architecture in
  [`Amort/Distributed/Distributed.md`](Amort/Distributed/Distributed.md).

## Building and Verification

```bash
lake build
```

Full build executes with 0 warnings and 0 errors across 2141 jobs. All theorems rely exclusively on standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`) with 0 `sorryAx`.

## Disclaimer

This is a personal side project. The views, opinions, and formalizations expressed here are solely those of the author and do not represent or reflect the views, positions, or endorsements of the author's employer (Google LLC). Any rights or intellectual property may be subject to employer agreements, but this project is not an official Google product.
