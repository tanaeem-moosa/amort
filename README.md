# amort

AI-assisted formalization of time complexity and correctness of algorithms in Lean 4.

## Verification Status Overview

This repository rigorously distinguishes between **fully verified algorithmic canons** (Phases 1 & 2 and §7.3 immediate acceptance targets) and **specification stubs** (Phases 3 & 4 awaiting full algorithmic verification):

| Domain | Fully Verified Modules (0 axioms beyond Lean standard) | Phase 3 & 4 Specification Stubs (`Status: stub — not verified`) |
| :--- | :--- | :--- |
| **GCD** | Binary GCD (`Nat.binaryGcd`), Euclidean GCD (`Nat.euclidGcd`), Asymptotics | — |
| **Sorting** | Insertion Sort, Merge Sort, Quicksort worst-case, Decision Trees, $\Omega(n \log n)$ Lower Bound | — |
| **Recurrences** | Telescoping, Halving, Divide-and-Conquer Master Theorem, Binary Search (`binarySearch_some_get`) | DP state-space model |
| **Data Structures** | Dynamic Array (amortized push $\le 3$), Two-Stack Queue (amortized pop $\le 1$, FIFO correctness) | Binary Heap / Heapsort, Balanced BST, Online Median, DS Asymptotics |
| **Strings** | Naive Match, KMP (`computePiLoop`, `kmpScan`, `mem_kmpMatch_iff`), LCS, Edit Distance | Trie, Aho-Corasick, Z-Algorithm, Rabin-Karp, Suffix Array, Ukkonen Suffix Tree |
| **Dynamic Programming** | 0/1 Knapsack (`knapsackWithCount` table fill, optimality), LIS (`lis_is_optimal`) | Matrix Chain Multiplication, DP Asymptotics |
| **Graphs** | BFS (`bfsLoop` two-sided distance, in-loop step count), Bellman-Ford (ℤ-weights, optimality, negative cycle) | Floyd-Warshall, Dijkstra, Max-Flow / Edmonds-Karp, SCC, Eulerian, Topological Sort, DSU, Kruskal, Prim, Ackermann DSU, Hopcroft-Karp, Tarjan Bridge, Hall's Marriage |
| **Greedy** | Interval Scheduling (internal sort, exchange-argument optimality) | Huffman Coding, Median-of-Medians (BFPRT) |
| **Number Theory** | Modular Exponentiation (`modExpWithCount`), Extended GCD (Bézout coefficients) | Sieve of Eratosthenes |
| **Complexity & LP** | 3-SAT to Independent Set reduction, 2-SAT characterization, LP Weak Duality | Complexity Classes P vs NP, Simplex Algorithm, LP Asymptotics |
| **Algebraic / Geo / Rand** | — | FFT, Strassen, Convex Hull, Closest Pair, Expected Quicksort, Karger Min-Cut, Universal Hashing |
| **Distributed** | — | Causality / Vector Clocks, Consensus (Paxos/Raft), BFT (PBFT/OM), Snapshot (Chandy-Lamport), Impossibility |

All 77 headline theorems of the verified modules are validated in `Amort/Audit.lean` and depend strictly on foundational Lean 4 axioms (`[propext, Classical.choice, Quot.sound]`) with 0 `sorryAx`, 0 `sorry`, and 0 `admit`. All unverified modules in Phases 3 and 4 are explicitly labeled with `Status: stub — not verified` banners in their `.lean` source and `.md` documentation.

---

## Modules Overview

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
- **Halving Recurrences & Binary Search**: `Amort.Recurrence.Halving` and `Amort.Recurrence.BinarySearch` with bit-length reduction $\text{size}(n/2) = \text{size } n - 1$, halving recurrence bounds $T(n) \le c \cdot \text{size } n + T(1)$, logarithmic bridge $\text{size } n = O(\log n)$, executable array and list binary search (`binarySearch`, `binarySearchArray`), correctness equivalence `binarySearch_isSome_iff`, index probe correctness `binarySearch_some_get`, instrumented probe counters (`binarySearchWithCount`, `binarySearchArrayWithCount`), and $O(\log n)$ complexity. Documented in [`Amort/Recurrence/HalvingAndBinarySearch.md`](Amort/Recurrence/HalvingAndBinarySearch.md).
- **Divide-and-Conquer Master Recurrence**: `Amort.Recurrence.MasterTheorem` formalizing balanced divide-and-conquer recurrences with integer rounding ($T(n) \le T(\lceil n/2 \rceil) + T(\lfloor n/2 \rfloor) + c \cdot n$), proving dyadic bounds $T(n) \le T(1) n + c n k$, $O(n \log n)$ asymptotics, and connecting to Merge Sort. Documented in [`Amort/Recurrence/MasterTheorem.md`](Amort/Recurrence/MasterTheorem.md).
- **State-Space Dynamic Programming**: *(Status: stub — not verified)* `Amort.Recurrence.DP` formalizing general finite state-space DP complexity ($	ext{totalCost} \le |S| \cdot C$) and 2D grid DP specialization as an abstract framework. Documented in [`Amort/Recurrence/DP.md`](Amort/Recurrence/DP.md).
- **Documentation**: Suite overview in [`Amort/Recurrence/Recurrence.md`](Amort/Recurrence/Recurrence.md).

### 8. Textbook String Algorithms (`Amort.String`)

> **Status: partially verified / contains stubs** (Naive Match, KMP, LCS, and Edit Distance are fully verified; Trie, Aho-Corasick, Z-Algorithm, Rabin-Karp, and Suffix Array are Phase 3/4 canon stubs awaiting full verification).

- **Naive String Matching**: `Amort.String.NaiveMatch` formalizing sliding-window matching, character comparison counting, concrete upper bound $\le (n - m + 1) \cdot m \le n \cdot m$, and substring occurrence correctness. Documented in [`Amort/String/NaiveMatch.md`](Amort/String/NaiveMatch.md).
- **Knuth-Morris-Pratt (KMP)**: `Amort.String.KMP` formalizing genuine failure table construction `computePiLoop` / `computePiWithCount` without brute-force delegation, preprocessing equivalence `computePi_getD`, preprocessing bound $\le 2m$, amortized potential function $\Phi(j) = j$ proving scanning bound $\le 2n$ via `kmpScan`, instrumented runtime `kmpWithCount`, combined linear bound $\le 2(n + m)$, and two-sided correctness equivalence `mem_kmpMatch_iff : s ∈ kmpMatch P T ↔ IsSubstringAt P T s`. Documented in [`Amort/String/KMP.md`](Amort/String/KMP.md).
- **Longest Common Subsequence (LCS)**: `Amort.String.LCS` formalizing recursive formulation, constructive maximal common subsequence witness, complete optimality characterization (`lcs_is_optimal`), bottom-up $(n + 1) \times (m + 1)$ dynamic programming table `lcsTable`, equivalence proof `lcsTable_eval`, instrumented execution counter `lcsWithCount` counting real cell fills, and concrete operation bound $\le (n + 1) \cdot (m + 1)$ ($O(n \cdot m)$). Documented in [`Amort/String/LCS.md`](Amort/String/LCS.md).
- **Edit Distance (Levenshtein Distance)**: `Amort.String.EditDistance` formalizing recursive edit distance, explicit alignment operations and cost, minimal-cost alignment correctness proof, bottom-up $(n + 1) \times (m + 1)$ dynamic programming matrix, instrumented execution counter `editDistWithCount`, and concrete step bound $\le (n + 1) \cdot (m + 1)$ ($O(n \cdot m)$). Documented in [`Amort/String/EditDistance.md`](Amort/String/EditDistance.md).
- **Prefix Trie**: *(Status: stub — not verified)* `Amort.String.Trie` formalizing prefix trie representation with child transitions and word termination markers (specification stub awaiting full dictionary lookup verification). Documented in [`Amort/String/Trie.md`](Amort/String/Trie.md).
- **Aho-Corasick Automaton**: *(Status: stub — not verified)* `Amort.String.AhoCorasick` formalizing failure links and depth potential bound $\le 2|T|$ (specification stub awaiting failure link construction and match emission). Documented in [`Amort/String/AhoCorasick.md`](Amort/String/AhoCorasick.md).
- **Gusfield's Z-Algorithm**: *(Status: stub — not verified)* `Amort.String.ZAlgorithm` formalizing $Z$-array specification $zSpec$ and pattern matching reduction $Z(P \$ T)$ (specification stub awaiting Z-box execution loop). Documented in [`Amort/String/ZAlgorithm.md`](Amort/String/ZAlgorithm.md).
- **Rabin-Karp Rolling Hash**: *(Status: stub — not verified)* `Amort.String.RabinKarp` formalizing polynomial rolling hash modulo prime $p$ and $O(1)$ sliding window update identity (specification stub awaiting Las Vegas verification matcher). Documented in [`Amort/String/RabinKarp.md`](Amort/String/RabinKarp.md).
- **Suffix Array & Kasai's LCP**: *(Status: stub — not verified)* `Amort.String.SuffixArray` formalizing suffix orderings, inverse permutation ranks, and Kasai's height decrement invariant (specification stub awaiting suffix sorting and LCP execution). Documented in [`Amort/String/SuffixArray.md`](Amort/String/SuffixArray.md).
- **Asymptotics & Composition Bridges**: `Amort.String.Asymptotics` connecting 2D table bounds to `Amort.Recurrence.Composition` (`isBigO_nested_loops_nat`), linear KMP bounds to `isBigO_sequential_add_nat`, and proving formal $O(n \cdot m)$ and $O(n + m)$ `IsBigO` bounds under `Filter.atTop`.
- **Advanced Asymptotics Bridges**: *(Status: stub — not verified)* `Amort.String.AdvancedAsymptotics` connecting Trie, Aho-Corasick, Z-Algorithm, Rabin-Karp, and Kasai specification bounds to Mathlib `IsBigO` under `Filter.atTop` (stub models). Documented in [`Amort/String/AdvancedAsymptotics.md`](Amort/String/AdvancedAsymptotics.md).

### 9. Textbook Dynamic Programming Algorithms (`Amort.DP`)

> **Status: partially verified / contains stubs** (0/1 Knapsack and LIS are fully verified; Matrix Chain is a Phase 3 canon stub awaiting table dynamic programming verification).

- **Grid DP: 0/1 Knapsack**: `Amort.DP.Knapsack` formalizing item weights and values, capacity $W$, Bellman recurrence, mathematical correctness against subcollections (soundness, completeness, optimality), explicit bottom-up row DP (`knapsackRow`) and table (`knapsackTable`) with equivalence proof `knapsackRow_eval`, instrumented execution counter `knapsackWithCount` accumulating $(W + 1)$ operations per row, and $O(n \cdot W)$ bound. Documented in [`Amort/DP/Knapsack.md`](Amort/DP/Knapsack.md).
- **Predecessor State-Space DP: Longest Increasing Subsequence**: `Amort.DP.LIS` formalizing strictly increasing sublists, prefix/recursive formulations, and mathematical correctness proof (`lis_is_optimal`). Documented in [`Amort/DP/LIS.md`](Amort/DP/LIS.md).
- **Interval DP: Matrix Chain Multiplication**: *(Status: stub — not verified)* `Amort.DP.MatrixChain` formalizing matrix dimensions, Bellman recurrence, and interval state space (specification stub awaiting parenthesization dynamic programming verification). Documented in [`Amort/DP/MatrixChain.md`](Amort/DP/MatrixChain.md).
- **Asymptotic Complexity Bridges**: *(Status: stub — not verified)* `Amort.DP.Asymptotics` connecting Matrix Chain ($O(n^3)$), 0/1 Knapsack ($O(n \cdot W)$), and LIS ($O(n^2)$) to Mathlib `IsBigO` under `Filter.atTop` (stub models).

### 10. Textbook Graph Algorithms (`Amort.Graph`)

> **Status: partially verified / contains stubs** (BFS traversal and Bellman-Ford are fully verified; Dijkstra, Max-Flow, SCC, Eulerian, Topological Sort, DSU, Kruskal, and Prim are Phase 3/4 canon stubs awaiting full verification).

- **Linear Graph Traversals & Handshaking (BFS)**: `Amort.Graph.Traversal` formalizing adjacency list representations, the directed Handshaking Lemma $\sum_{v} \text{outdeg}(v) = |E|$, executable queue/visited BFS loop `bfsLoop` returning genuine accumulated distance maps in base cases, two-sided shortest path distance correctness (`bfs_eq_top_iff`, `bfs_eq_coe_iff`), distance walk soundness `bfsWithCount_walk`, fuel exhaustiveness `bfs_fuel_exhaustion_le`, and in-loop instrumented execution counter `bfsWithCount` bounded by $|V| + |E|$ without clamping. Documented in [`Amort/Graph/Traversal.md`](Amort/Graph/Traversal.md).
- **Bellman-Ford Shortest Paths**: `Amort.Graph.BellmanFord` formalizing single-source shortest paths with integer $\mathbb{Z}$ weights via $(n - 1)$ edge relaxation passes, proving path realizability `bellmanFord_achieved`, shortest-path optimality under independent `NoNegCycle` (`bellmanFord_optimal`), negative cycle detection `hasNegCycleCheck_iff`, step bound $(n - 1) \cdot |E| \le n \cdot |E|$, and $O(|V| \cdot |E|)$ complexity. Documented in [`Amort/Graph/BellmanFord.md`](Amort/Graph/BellmanFord.md).
- **Floyd-Warshall Shortest Paths**: *(Status: stub — not verified)* `Amort.Graph.FloydWarshall` formalizing all-pairs shortest paths via 3D dynamic programming state space (specification stub awaiting bottom-up table verification). Documented in [`Amort/Graph/FloydWarshall.md`](Amort/Graph/FloydWarshall.md).
- **Dijkstra's Shortest Paths**: *(Status: stub — not verified)* `Amort.Graph.Dijkstra` formalizing single-source shortest paths for non-negative edge weights and greedy choice invariant (specification stub awaiting executable priority queue implementation). Documented in [`Amort/Graph/Dijkstra.md`](Amort/Graph/Dijkstra.md).
- **Network Flow & Max-Flow Min-Cut Theorem**: *(Status: stub — not verified)* `Amort.Graph.MaxFlow` formalizing flow networks, capacity constraints, conservation, the Cut-Flow Identity, and Weak Duality (specification stub awaiting augmenting path execution and Edmonds-Karp bounds). Documented in [`Amort/Graph/MaxFlow.md`](Amort/Graph/MaxFlow.md).
- **Strongly Connected Components (SCC)**: *(Status: stub — not verified)* `Amort.Graph.SCC` formalizing directed reachability, mutual reachability equivalence classes, and condensation DAG acyclicity (specification stub awaiting Kosaraju/Tarjan DFS traversal execution). Documented in [`Amort/Graph/SCC.md`](Amort/Graph/SCC.md).
- **Eulerian Circuits & Hierholzer's Algorithm**: *(Status: stub — not verified)* `Amort.Graph.Eulerian` formalizing the in-degree Handshaking equality and degree balance conditions (specification stub awaiting Hierholzer cycle splicing execution). Documented in [`Amort/Graph/Eulerian.md`](Amort/Graph/Eulerian.md).
- **Topological Sort**: *(Status: stub — not verified)* `Amort.Graph.TopologicalSort` formalizing topological ordering and DAG cycle-freedom (specification stub awaiting Kahn queue algorithm execution). Documented in [`Amort/Graph/TopologicalSort.md`](Amort/Graph/TopologicalSort.md).
- **Disjoint Set Union (Union-Find)**: *(Status: stub — not verified)* `Amort.Graph.DSU` formalizing union-by-rank and exponential subtree size invariant $2^{\text{rank}} \le n$ (specification stub awaiting executable union-by-rank and find operations). Documented in [`Amort/Graph/DSU.md`](Amort/Graph/DSU.md).
- **Kruskal's Minimum Spanning Tree**: *(Status: stub — not verified)* `Amort.Graph.Kruskal` formalizing edge sorting via `Amort.Sorting.MergeSort` (specification stub awaiting spanning forest cut property and DSU cycle checking execution). Documented in [`Amort/Graph/Kruskal.md`](Amort/Graph/Kruskal.md).
- **Prim's Minimum Spanning Tree**: *(Status: stub — not verified)* `Amort.Graph.Prim` formalizing priority queue frontier selection and Cut-Property invariant (specification stub awaiting executable priority queue frontier implementation). Documented in [`Amort/Graph/Prim.md`](Amort/Graph/Prim.md).
- **Asymptotic Complexity Bridges**: `Amort.Graph.Asymptotics` and `Amort.Graph.AdvancedAsymptotics` connecting Bellman-Ford ($O(|V| \cdot |E|)$) to Mathlib `IsBigO`, while remaining theorems serve as specification stub models.

### 11. Textbook Data Structures & Online Query Algorithms (`Amort.DataStructure`)

> **Status: partially verified / contains stubs** (Dynamic Array and Two-Stack Queue are fully verified; Binary Heap, Online Median, and Balanced BST are Phase 3 canon stubs awaiting full algorithmic verification).

- **Dynamic Array Capacity Doubling**: `Amort.DataStructure.DynamicArray` formalizing capacity doubling, potential function $\Phi = 2n - C$, amortized push $\hat{c} \le 3$, non-negativity $\Phi \ge 0$, and multi-operation telescoping bound from `initOne` without unconstructed hypotheses (`pushSeqCost_telescope_initOne`, `pushSeqCost_initOne_le`). Documented in [`Amort/DataStructure/DynamicArray.md`](Amort/DataStructure/DynamicArray.md).
- **Two-Stack FIFO Queue**: `Amort.DataStructure.TwoStackQueue` formalizing two-stack FIFO queue, potential function $\Phi = 2 \cdot |\text{inStack}|$, amortized push $\hat{c} = 3$, amortized pop $\hat{c} \le 1$, sequence append soundness, FIFO functional correctness (`pop_fst`, `pop_snd_toList`, `pop_spec`), and multi-operation telescoping bound (`totalActualCost_le_three_mul`). Documented in [`Amort/DataStructure/TwoStackQueue.md`](Amort/DataStructure/TwoStackQueue.md).
- **Binary Heaps & Heapsort**: *(Status: stub — not verified)* `Amort.DataStructure.BinaryHeap` formalizing binary heap order invariants, root minimality, and linear build-heap theorem $\sum (n / 2^h) h \le 2n$ (specification stub awaiting array siftUp/siftDown operations). Documented in [`Amort/DataStructure/BinaryHeap.md`](Amort/DataStructure/BinaryHeap.md).
- **Online Running Median with Dual Heaps**: *(Status: stub — not verified)* `Amort.DataStructure.OnlineMedian` formalizing dual-heap streaming model and mathematical median soundness (specification stub awaiting heap insertion/rebalancing operations). Documented in [`Amort/DataStructure/OnlineMedian.md`](Amort/DataStructure/OnlineMedian.md).
- **Balanced Binary Search Trees**: *(Status: stub — not verified)* `Amort.DataStructure.BalancedBST` formalizing height-balanced BSTs with size annotations and tree rotations preserving BST ordering (specification stub awaiting rebalancing insert/delete operations). Documented in [`Amort/DataStructure/BalancedBST.md`](Amort/DataStructure/BalancedBST.md).
- **Asymptotic Complexity Bridges**: *(Status: stub — not verified)* `Amort.DataStructure.Asymptotics` connecting heap, median, and BST closed-form formulas to Mathlib `IsBigO` (stub models).

### 12. Greedy Algorithms & Linear Selection (`Amort.Greedy`)

> **Status: partially verified / contains stubs** (Interval Scheduling is fully verified; Huffman Coding and Median-of-Medians are Phase 3 canon stubs awaiting full verification).

- **Interval Scheduling / Activity Selection**: `Amort.Greedy.IntervalScheduling` formalizing compatible intervals $start < finish$, greedy earliest-finish-time selection, end-to-end exchange argument optimality from unsorted inputs (`intervalSchedule_optimal`), instrumented step counter `intervalScheduleWithCount`, and $O(n \log n)$ operational bound dominated by sorting. Documented in [`Amort/Greedy/IntervalScheduling.md`](Amort/Greedy/IntervalScheduling.md).
- **Huffman Coding & Optimal Prefix Trees**: *(Status: stub — not verified)* `Amort.Greedy.Huffman` formalizing weighted symbol alphabets and external path length equivalence (specification stub awaiting prefix tree construction algorithm). Documented in [`Amort/Greedy/Huffman.md`](Amort/Greedy/Huffman.md).
- **Median-of-Medians Deterministic Selection (BFPRT)**: *(Status: stub — not verified)* `Amort.Greedy.MedianOfMedians` formalizing group-of-5 partitioning and linear-time divide-and-conquer recurrence (specification stub awaiting selection execution algorithm). Documented in [`Amort/Greedy/MedianOfMedians.md`](Amort/Greedy/MedianOfMedians.md).
- **Asymptotic Complexity Bridges**: `Amort.Greedy.Asymptotics` connecting Interval Scheduling ($O(n \log n)$) to Mathlib `IsBigO`, while Huffman and BFPRT bounds serve as specification stub models.

### 13. Computational Geometry (`Amort.Geometry`)

> **Status: stub — not verified** (Phase 4 canon stubs; Convex Hull and Closest Pair algorithms are specification stubs awaiting full verification).

- **2D Convex Hull (Graham Scan / Monotone Chain)**: *(Status: stub — not verified)* `Amort.Geometry.ConvexHull` formalizing 2D points, orientation determinant cross product, and monotone chain stack invariants (specification stub awaiting Graham scan execution). Documented in [`Amort/Geometry/ConvexHull.md`](Amort/Geometry/ConvexHull.md).
- **Closest Pair of Points**: *(Status: stub — not verified)* `Amort.Geometry.ClosestPair` formalizing squared Euclidean distance, strip geometric sparsity lemma, and divide-and-conquer recurrence (specification stub awaiting divide-and-conquer execution algorithm). Documented in [`Amort/Geometry/ClosestPair.md`](Amort/Geometry/ClosestPair.md).
- **Asymptotic Complexity Bridges**: *(Status: stub — not verified)* `Amort.Geometry.Asymptotics` connecting Convex Hull and Closest Pair closed-form bounds to Mathlib `IsBigO` (stub models).

### 14. Number Theoretic Algorithms (`Amort.NumberTheory`)

> **Status: partially verified / contains stubs** (Modular Exponentiation and Extended GCD are fully verified; Sieve of Eratosthenes is a Phase 3 canon stub awaiting full verification).

- **Fast Modular Exponentiation (Binary Exponentiation)**: `Amort.NumberTheory.ModExp` formalizing repeated squaring computing $a^b \bmod m$, loop state correctness invariant $acc \cdot base^{exp} \equiv a^b \pmod m$, instrumented execution counter `modExpWithCount`, and logarithmic step bound $\le 2 \cdot \text{Nat.size } b \implies O(\log b)$. Documented in [`Amort/NumberTheory/ModExp.md`](Amort/NumberTheory/ModExp.md).
- **Extended Euclidean Algorithm**: `Amort.NumberTheory.ExtendedGCD` formalizing extended Euclidean division computing Bézout coefficients $x, y \in \mathbb{Z}$ satisfying $a \cdot x + b \cdot y = \gcd(a, b)$ (`extGCD_bezout`), equivalence to `Nat.gcd` (`extGCD_gcd`), two-step remainder halving theorem $2 \cdot r_{k+2} < r_k$, and logarithmic step bound. Documented in [`Amort/NumberTheory/ExtendedGCD.md`](Amort/NumberTheory/ExtendedGCD.md).
- **Sieve of Eratosthenes**: *(Status: stub — not verified)* `Amort.NumberTheory.Sieve` formalizing prime characterization (specification stub awaiting array composite marking algorithm). Documented in [`Amort/NumberTheory/Sieve.md`](Amort/NumberTheory/Sieve.md).
- **Asymptotic Complexity Bridges**: `Amort.NumberTheory.Asymptotics` connecting ModExp ($O(\log b)$) and Extended GCD ($O(\log(\min a\ b))$) to Mathlib `IsBigO` under `Filter.atTop`.

### 15. Fast Algebraic & Divide-and-Conquer Algorithms (`Amort.Algebraic`)

> **Status: stub — not verified** (Phase 3/4 canon stubs; FFT and Strassen matrix multiplication algorithms are specification stubs awaiting full verification).

- **Fast Fourier Transform (FFT)**: *(Status: stub — not verified)* `Amort.Algebraic.FFT` formalizing roots of unity, cancellation lemma, Cooley-Tukey Radix-2 decomposition, and butterfly operation correctness (specification stub awaiting recursive list FFT execution and DFT equivalence). Documented in [`Amort/Algebraic/FFT.md`](Amort/Algebraic/FFT.md).
- **Strassen's Sub-Cubic Matrix Multiplication**: *(Status: stub — not verified)* `Amort.Algebraic.Strassen` formalizing $2 \times 2$ block matrices over arbitrary rings, Strassen's 7 auxiliary multiplications, and algebraic equivalence theorem (specification stub awaiting block matrix recurrence execution). Documented in [`Amort/Algebraic/Strassen.md`](Amort/Algebraic/Strassen.md).
- **Asymptotic Complexity Bridges**: *(Status: stub — not verified)* `Amort.Algebraic.Asymptotics` connecting FFT and Strassen closed-form bounds to Mathlib `IsBigO` (stub models).

### 16. NP-Completeness, Complexity Classes & Classical Reductions (`Amort.Complexity`)

> **Status: partially verified / contains stubs** (3-SAT to Independent Set reduction and 2-SAT characterization are fully verified; Complexity Classes P and NP are Phase 0 canon stubs).

- **Karp's Foundational Reductions & Complement Duality**: `Amort.Complexity.KarpReductions` formalizing simple graphs, Independent Set, Vertex Cover, Clique, Complement Duality theorem ($S \text{ IS} \iff S^c \text{ VC} \iff S \text{ Clique in } \overline{G}$), and 3-SAT to Independent Set clause triangle gadget reduction soundness and completeness (`sat3_to_independentSet_correct`). Documented in [`Amort/Complexity/KarpReductions.md`](Amort/Complexity/KarpReductions.md).
- **2-SAT Linear-Time Solver via SCC**: `Amort.Complexity.TwoSAT` formalizing 2-CNF boolean logic, implication digraph, contrapositive symmetry, connection to `Amort.Graph.SCC`, and soundness and completeness theorem proving a 2-CNF formula is satisfiable iff no variable $x$ lies in the same SCC as $\neg x$ (`twoSAT_soundness_and_completeness`). Documented in [`Amort/Complexity/TwoSAT.md`](Amort/Complexity/TwoSAT.md).
- **Complexity Classes P and NP**: *(Status: stub — not verified)* `Amort.Complexity.Classes` formalizing languages over alphabets, canonical polynomial bounds, and polynomial verifiers (Phase 0 canon stub; abstract machine model). Documented in [`Amort/Complexity/Classes.md`](Amort/Complexity/Classes.md).
- **Asymptotic Complexity Bridges**: *(Status: stub — not verified)* `Amort.Complexity.Asymptotics` connecting reduction graph size formulas to Mathlib `IsBigO` (stub models).

### 17. Approximation Algorithms (`Amort.Approximation`)

> **Status: stub — not verified** (Phase 4 canon stubs; Vertex Cover, Metric TSP, and Set Cover algorithms are specification stubs awaiting full verification).

- **Vertex Cover 2-Approximation**: *(Status: stub — not verified)* `Amort.Approximation.VertexCover` formalizing greedy maximal matching lower bound $|M| \le |C^*|$ and approximation ratio $|C| \le 2|C^*|$ (specification stub awaiting maximal matching execution algorithm). Documented in [`Amort/Approximation/VertexCover.md`](Amort/Approximation/VertexCover.md).
- **Metric TSP 2-Approximation**: *(Status: stub — not verified)* `Amort.Approximation.MetricTSP` formalizing metric triangle inequality and shortcutting theorem (specification stub awaiting shortcutting execution algorithm). Documented in [`Amort/Approximation/MetricTSP.md`](Amort/Approximation/MetricTSP.md).
- **Set Cover Greedy $H(n)$-Approximation**: *(Status: stub — not verified)* `Amort.Approximation.SetCover` formalizing harmonic numbers, marginal charging scheme, and harmonic potential bound $|\mathcal{C}_{\text{greedy}}| \le H(n) \cdot \text{OPT}$ (specification stub awaiting greedy subset extraction algorithm). Documented in [`Amort/Approximation/SetCover.md`](Amort/Approximation/SetCover.md).
- **Asymptotic Complexity Bridges**: *(Status: stub — not verified)* `Amort.Approximation.Asymptotics` connecting approximation step bounds to Mathlib `IsBigO` (stub models).

### 18. Advanced Graph Algorithms & Bipartite Matching (`Amort.Graph.Advanced`)

> **Status: stub — not verified** (Phase 4 canon stubs; Hopcroft-Karp, Hall's Marriage, and Tarjan DFS bridge finding are specification stubs awaiting full verification).

- **Hopcroft-Karp Maximum Bipartite Matching**: *(Status: stub — not verified)* `Amort.Graph.Advanced.HopcroftKarp` formalizing bipartite graphs, alternating paths, and augmenting path phase bounds (specification stub awaiting phased BFS/DFS execution). Documented in [`Amort/Graph/Advanced/HopcroftKarp.md`](Amort/Graph/Advanced/HopcroftKarp.md).
- **Hall's Marriage Theorem**: *(Status: stub — not verified)* `Amort.Graph.Advanced.HallMarriage` formalizing bipartite graphs and Hall neighborhood condition necessity (specification stub awaiting sufficiency reduction). Documented in [`Amort/Graph/Advanced/HallMarriage.md`](Amort/Graph/Advanced/HallMarriage.md).
- **Bridges & Articulation Points (Tarjan's DFS)**: *(Status: stub — not verified)* `Amort.Graph.Advanced.BridgeTarjan` formalizing DFS discovery order and bridge characterization (specification stub awaiting DFS tree traversal and low-link algorithms). Documented in [`Amort/Graph/Advanced/BridgeTarjan.md`](Amort/Graph/Advanced/BridgeTarjan.md).
- **Asymptotic Complexity Bridges**: *(Status: stub — not verified)* `Amort.Graph.Advanced.Asymptotics` connecting Hopcroft-Karp and Tarjan bridge finding to Mathlib `IsBigO` (stub models).

### 19. Randomized Algorithms & Probabilistic Complexity (`Amort.Randomized`)

> **Status: stub — not verified** (Phase 4 canon stubs; Expected Quicksort, Karger Min-Cut, and Universal Hashing algorithms are specification stubs awaiting full verification on Mathlib PMF).

- **Expected Complexity of Randomized Quicksort**: *(Status: stub — not verified)* `Amort.Randomized.Quicksort` formalizing comparison indicators $X_{ij}$, pivot probability lemma, and harmonic bound $\mathbb{E}[C] \le 2n H(n)$ (specification stub awaiting randomized execution on Mathlib PMF). Documented in [`Amort/Randomized/Quicksort.md`](Amort/Randomized/Quicksort.md).
- **Karger's Min-Cut Contraction Algorithm**: *(Status: stub — not verified)* `Amort.Randomized.KargerMinCut` formalizing multigraph contraction and telescoping contraction survival probability (specification stub awaiting randomized graph contraction on PMF). Documented in [`Amort/Randomized/KargerMinCut.md`](Amort/Randomized/KargerMinCut.md).
- **Universal Hashing & Reservoir Sampling**: *(Status: stub — not verified)* `Amort.Randomized.UniversalHash` formalizing 2-Universal hash families and collision probability bounds (specification stub awaiting concrete hash family construction on PMF). Documented in [`Amort/Randomized/UniversalHash.md`](Amort/Randomized/UniversalHash.md).
- **Asymptotic Complexity Bridges**: *(Status: stub — not verified)* `Amort.Randomized.Asymptotics` connecting randomized algorithm bounds to Mathlib `IsBigO` (stub models).

### 20. Linear Programming & Duality (`Amort.LP`)

> **Status: partially verified / contains stubs** (Weak Duality and Optimality Certificates are fully verified; Simplex dictionary pivot and Bland termination are Phase 4 canon stubs).

- **Primal and Dual Formulations**: `Amort.LP.Duality` formalizing linear programs in standard inequality form over vectors ($Ax \le b, x \ge 0$ and $A^T y \ge c, y \ge 0$), with feasibility predicates `PrimalFeasible` and `DualFeasible`. Documented in [`Amort/LP/Duality.md`](Amort/LP/Duality.md).
- **Weak Duality & Optimality Certificates**: Formal proofs of `weak_duality` ($c^T x \le b^T y$), `optimality_certificate` ($c^T x^* = b^T y^* \implies \text{OPT}$), and unboundedness infeasibility corollaries (`dual_infeasible_of_unbounded_primal`, `primal_infeasible_of_unbounded_dual`).
- **Simplex Slack Form & Dictionary Invariant**: *(Status: stub — not verified)* `Amort.LP.Simplex` formalizing dictionary representations $x_B = \bar{b} - \bar{A} x_N$, basic solution feasibility invariant $\bar{b} \ge 0$, and ratio test bounds (specification stub awaiting dictionary pivot loop and Bland termination). Documented in [`Amort/LP/Simplex.md`](Amort/LP/Simplex.md).
- **Asymptotic Complexity Bridges**: *(Status: stub — not verified)* `Amort.LP.Asymptotics` connecting simplex pivot step bounds to Mathlib `IsBigO` (stub models). Documented in [`Amort/LP/Asymptotics.md`](Amort/LP/Asymptotics.md).

### 21. Tarjan's Inverse Ackermann Bound for DSU (`Amort.Graph.Ackermann`)

> **Status: stub — not verified** (Phase 4 canon stubs; rank invariants and potential bounds are specification stubs awaiting operational sequence execution).

- **Ackermann Hierarchy & Functional Inverse**: *(Status: stub — not verified)* `Amort.Graph.Ackermann.AckermannHierarchy` formalizing two-variable Ackermann function $A_k(n)$, strict monotonicity, and milestone evaluations (specification stub awaiting functional unbounded inverse). Documented in [`Amort/Graph/Ackermann/AckermannHierarchy.md`](Amort/Graph/Ackermann/AckermannHierarchy.md).
- **Path Compression with Union-by-Rank**: *(Status: stub — not verified)* `Amort.Graph.Ackermann.PathCompression` formalizing DSU with path compression during `find` (specification stub awaiting operational sequence execution). Documented in [`Amort/Graph/Ackermann/PathCompression.md`](Amort/Graph/Ackermann/PathCompression.md).
- **Potential Function Analysis & Amortized Bound**: *(Status: stub — not verified)* `Amort.Graph.Ackermann.PotentialBound` formalizing rank level intervals and potential function telescoping summation (specification stub awaiting operational work bounds). Documented in [`Amort/Graph/Ackermann/PotentialBound.md`](Amort/Graph/Ackermann/PotentialBound.md).
- **Asymptotic Complexity Bridges**: *(Status: stub — not verified)* `Amort.Graph.Ackermann.Asymptotics` connecting Ackermann DSU work bounds to Mathlib `IsBigO` and `IsTheta` (stub models). Documented in [`Amort/Graph/Ackermann/Asymptotics.md`](Amort/Graph/Ackermann/Asymptotics.md).

### 22. Suffix Trees & Ukkonen's Online Linear-Time Construction (`Amort.String.SuffixTree`)

> **Status: stub — not verified** (Phase 4 canon stubs; compact suffix tree and Ukkonen construction are specification stubs awaiting operational execution).

- **Compact Suffix Tree Structure**: *(Status: stub — not verified)* `Amort.String.SuffixTree.CompactTree` formalizing slice intervals $[l, r]$, internal branching degree $\ge 2$, and node bounds (specification stub awaiting tree construction algorithm). Documented in [`Amort/String/SuffixTree/CompactTree.md`](Amort/String/SuffixTree/CompactTree.md).
- **Suffix Links & Depth Invariants**: *(Status: stub — not verified)* `Amort.String.SuffixTree.SuffixLink` formalizing suffix links mapping $a \beta$ to $\beta$ and depth decrement invariants (specification stub awaiting link construction algorithm). Documented in [`Amort/String/SuffixTree/SuffixLink.md`](Amort/String/SuffixTree/SuffixLink.md).
- **Ukkonen's Online Algorithm & $O(n)$ Bound**: *(Status: stub — not verified)* `Amort.String.SuffixTree.Ukkonen` formalizing active point `(active_node, active_edge, active_len)` and the three extension rules (specification stub awaiting online tree construction execution). Documented in [`Amort/String/SuffixTree/Ukkonen.md`](Amort/String/SuffixTree/Ukkonen.md).
- **Asymptotic Complexity Bridges**: *(Status: stub — not verified)* `Amort.String.SuffixTree.Asymptotics` connecting Ukkonen operational work to Mathlib `IsBigO` (stub models). Documented in [`Amort/String/SuffixTree/Asymptotics.md`](Amort/String/SuffixTree/Asymptotics.md).

### 23. Disjoint Set Union with Path Compression Only (`Amort.Graph.PathCompressionOnly`)

> **Status: stub — not verified** (Phase 4 canon stub; two-pass compression post-condition is proven, but operational sequence bounds are specification formulas).

- **Minimal State & Arbitrary Linking**: *(Status: stub — not verified)* `Amort.Graph.DSUPCO` containing parent pointers only without rank or size arrays, with arbitrary linking `unite(u, v)`.
- **Iterative Two-Pass Path Compression**: `findPath`, `findRoot`, and `compressPath` re-pointing all traversed nodes directly to root, proving post-condition `path_depth_one_after_find`.
- **Worst-Case Operations & Asymptotic Bounds**: *(Status: stub — not verified)* Linear chain has depth $n - 1$ ($\Omega(n)$ depth); adversarial and amortized bounds are specification formulas awaiting sequence execution. Documented in [`Amort/Graph/PathCompressionOnly.md`](Amort/Graph/PathCompressionOnly.md).

### 24. Quicksort Algorithm Canon (`Amort.Sorting.Quicksort`)
- **Algorithmic Correctness**: 3-way partitioning (`partition3`), length-fueled recursion (`quicksortFuel`, `quicksort`), permutation equivalence (`quicksort_perm`), sortedness (`quicksort_sorted`, `quicksort_sortedLE`), and exact equivalence to Mathlib (`quicksort_eq_mergeSort`, `quicksort_eq_insertionSort`).
- **Worst-Case Quadratic Complexity**: `quicksortWorstCaseRec` step identity, exact closed-form solution $T(n) = n(n - 1) / 2$ (`quicksortWorstCaseRec_eq`), and tight $\Theta(n^2)$ asymptotics (`isTheta_quicksortWorstCase_sq`).
- **Instrumented Execution & Worst-Case Attainment**: Instrumented counter `quicksortWithCount`, functional correctness `(quicksortWithCount xs).1 = quicksort xs`, concrete upper bound `(quicksortWithCount xs).2 ≤ xs.length * (xs.length - 1) / 2`, exact quadratic attainment on replicate elements `(quicksortWithCount (List.replicate n x)).2 = n * (n - 1) / 2`, and Mathlib asymptotics bridge `isBigO_quicksortWithCount_snd_sq`.
- **Deterministic Median (BFPRT) & Average-Case Models**: *(Status: stub — not verified)* BFPRT partition balance and average-case indicators are specification formulas awaiting full Phase 3/4 execution. Documented in [`Amort/Sorting/Quicksort.md`](Amort/Sorting/Quicksort.md).

### 25. Foundational Distributed Systems Canon (`Amort.Distributed`)

> **Status: stub — not verified** (Phase 4 canon stubs; consensus, vector clocks, BFT, and snapshot protocols are specification stubs awaiting executable step transition rules).

- **Causality & Logical Clocks**: *(Status: stub — not verified)* `Amort.Distributed.Causality` formalizing distributed events, Lamport happens-before strict partial order, and Lamport scalar clock consistency (specification stub awaiting vector clock step execution rules). Documented in [`Amort/Distributed/Causality.md`](Amort/Distributed/Causality.md).
- **Impossibility Theorems**: *(Status: stub — not verified)* `Amort.Distributed.Impossibility` formalizing two-node CAP toy model and Two Generals' impossibility over lossy channels (specification stub awaiting full asynchronous consensus impossibility). Documented in [`Amort/Distributed/Impossibility.md`](Amort/Distributed/Impossibility.md).
- **Crash-Tolerant Consensus (Paxos & Raft)**: *(Status: stub — not verified)* `Amort.Distributed.Consensus` formalizing majority quorum intersection and Synod core invariant (specification stub awaiting Paxos P2 invariant and Raft log matching execution). Documented in [`Amort/Distributed/Consensus.md`](Amort/Distributed/Consensus.md).
- **Byzantine Fault Tolerance ($3f + 1$)**: *(Status: stub — not verified)* `Amort.Distributed.BFT` formalizing PBFT quorum intersection and Lamport-Shostak-Pease 3-node impossibility (specification stub awaiting OM(m) inductive protocol execution). Documented in [`Amort/Distributed/BFT.md`](Amort/Distributed/BFT.md).
- **Consistent Global Snapshots**: *(Status: stub — not verified)* `Amort.Distributed.Snapshot` formalizing FIFO marker-passing rules and consistent cut definitions (specification stub awaiting Chandy-Lamport protocol execution). Documented in [`Amort/Distributed/Snapshot.md`](Amort/Distributed/Snapshot.md).

## Building and Verification

```bash
lake build
lake build Amort.Audit
lake env lean Amort/Audit.lean
```

Full build executes with 0 warnings and 0 errors across 2142 jobs.
`Amort/Audit.lean` comprehensively checks `#print axioms` across all 77 headline theorems in the verified algorithmic domains. All theorems rely exclusively on standard foundational Lean axioms (`propext`, `Classical.choice`, `Quot.sound`) with 0 `sorryAx`, 0 `sorry`, and 0 `admit`.

## Disclaimer

This is a personal side project. The views, opinions, and formalizations expressed here are solely those of the author and do not represent or reflect the views, positions, or endorsements of the author's employer (Google LLC). Any rights or intellectual property may be subject to employer agreements, but this project is not an official Google product.
