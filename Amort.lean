/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Amort.GCD.BinaryGCD
import Amort.GCD.StepCount
import Amort.GCD.EuclideanGCD
import Amort.GCD.Asymptotics
import Amort.Sorting.InsertionSort
import Amort.Sorting.MergeSort
import Amort.Sorting.Asymptotics
import Amort.Sorting.Quicksort
import Amort.Sorting.DecisionTree
import Amort.Sorting.LowerBound
import Amort.Recurrence.Composition
import Amort.Recurrence.Telescoping
import Amort.Recurrence.Halving
import Amort.Recurrence.BinarySearch
import Amort.Recurrence.MasterTheorem
import Amort.Recurrence.DP
import Amort.String.NaiveMatch
import Amort.String.KMP
import Amort.String.LCS
import Amort.String.EditDistance
import Amort.String.Asymptotics
import Amort.String.Trie
import Amort.String.AhoCorasick
import Amort.String.ZAlgorithm
import Amort.String.RabinKarp
import Amort.String.SuffixArray
import Amort.String.AdvancedAsymptotics
import Amort.DP.MatrixChain
import Amort.DP.Knapsack
import Amort.DP.LIS
import Amort.DP.Asymptotics
import Amort.Graph.FloydWarshall
import Amort.Graph.BellmanFord
import Amort.Graph.Traversal
import Amort.Graph.TopologicalSort
import Amort.Graph.DSU
import Amort.Graph.Kruskal
import Amort.Graph.Asymptotics
import Amort.Graph.PathCompressionOnly
import Amort.Graph.Dijkstra
import Amort.Graph.MaxFlow
import Amort.Graph.SCC
import Amort.Graph.Eulerian
import Amort.Graph.Prim
import Amort.Graph.AdvancedAsymptotics
import Amort.DataStructure.BinaryHeap
import Amort.DataStructure.OnlineMedian
import Amort.DataStructure.BalancedBST
import Amort.DataStructure.DynamicArray
import Amort.DataStructure.TwoStackQueue
import Amort.DataStructure.Asymptotics
import Amort.Greedy.IntervalScheduling
import Amort.Greedy.Huffman
import Amort.Greedy.MedianOfMedians
import Amort.Greedy.Asymptotics
import Amort.Geometry.ConvexHull
import Amort.Geometry.ClosestPair
import Amort.Geometry.Asymptotics
import Amort.NumberTheory.ModExp
import Amort.NumberTheory.ExtendedGCD
import Amort.NumberTheory.Sieve
import Amort.NumberTheory.Asymptotics
import Amort.Algebraic.FFT
import Amort.Algebraic.Strassen
import Amort.Algebraic.Asymptotics
import Amort.Complexity.Classes
import Amort.Complexity.TwoSAT
import Amort.Complexity.KarpReductions
import Amort.Complexity.Asymptotics
import Amort.Approximation.VertexCover
import Amort.Approximation.MetricTSP
import Amort.Approximation.SetCover
import Amort.Approximation.Asymptotics
import Amort.Graph.Advanced.HopcroftKarp
import Amort.Graph.Advanced.HallMarriage
import Amort.Graph.Advanced.BridgeTarjan
import Amort.Graph.Advanced.Asymptotics
import Amort.Randomized.Quicksort
import Amort.Randomized.KargerMinCut
import Amort.Randomized.UniversalHash
import Amort.Randomized.Asymptotics
import Amort.LP.Duality
import Amort.LP.Simplex
import Amort.LP.Asymptotics
import Amort.Graph.Ackermann.AckermannHierarchy
import Amort.Graph.Ackermann.PathCompression
import Amort.Graph.Ackermann.PotentialBound
import Amort.Graph.Ackermann.Asymptotics
import Amort.String.SuffixTree.CompactTree
import Amort.String.SuffixTree.SuffixLink
import Amort.String.SuffixTree.Ukkonen
import Amort.String.SuffixTree.Asymptotics
import Amort.Distributed.Causality
import Amort.Distributed.Impossibility
import Amort.Distributed.Consensus
import Amort.Distributed.BFT
import Amort.Distributed.Snapshot
import Amort.Audit

/-!
# Amort: Formalized Algorithm Complexity in Lean 4

This library formalizes the time complexity and mathematical correctness of classical
algorithms, recurrence relations, and amortized data structures. Fully verified modules
(Phases 1 & 2, and §7.3 targets) include genuine executable algorithms, two-sided correctness,
and instrumented operational bounds, while Phase 3 & 4 modules serve as specification stubs
marked `Status: stub — not verified`.

## Modules
- `Amort.GCD.BinaryGCD`: Definition, invariant lemmas, and proof of equivalence
  for Stein's Binary GCD.
- `Amort.GCD.StepCount`: Step counting, instrumented representation, and bit-length
  logarithmic bounds for Binary GCD.
- `Amort.GCD.EuclideanGCD`: Step counting and logarithmic upper bounds for the
  standard Euclidean algorithm via modulo halving.
- `Amort.GCD.Asymptotics`: Bridges connecting concrete step bounds to Mathlib's
  `Asymptotics.IsBigO` framework.
- `Amort.Sorting.InsertionSort`: Comparison counting, instrumented representation, and
  concrete $O(n^2)$ comparison bounds for Insertion Sort.
- `Amort.Sorting.MergeSort`: Comparison counting, instrumented representation, divide-and-conquer
  recurrence bounds, and concrete $O(n \log n)$ bounds for Merge Sort.
- `Amort.Sorting.Asymptotics`: Bridges connecting concrete sorting comparison bounds to Mathlib's
  `Asymptotics.IsBigO` framework.
- `Amort.Sorting.Quicksort`: 3-way partitioning, length-fueled recursion, permutation equivalence,
  sortedness, Mathlib equivalence, worst-case $\Theta(n^2)$, deterministic median BFPRT
  worst-case $O(n \log n)$, and average-case expected $O(n \log n)$.
- `Amort.Sorting.DecisionTree`: Abstract binary decision tree model, depth, leaf count,
  structural induction bound `leafCount T ≤ 2 ^ depth T`, and tree evaluation.
- `Amort.Sorting.LowerBound`: Permutation coverage, factorial bound $n! \le 2^{\text{depth}}$,
  worst-case depth lower bound $\text{clog}_2(n!) \le \text{depth}$, combinatorial factorial
  growth bound, and asymptotic lower bound $\log(n!) = \Omega(n \log n)$ in Mathlib `IsBigO`.
- `Amort.Recurrence.Composition`: Compositional complexity algebra (nested loop products,
  sequential phase sums, maximum phase bounds, and phase dominance) in Mathlib `IsBigO`.
- `Amort.Recurrence.Telescoping`:
  Linear and power telescoping recurrences ($T(n+1) \le T(n) + f(n)$),
  constant and power step bounds ($O(n^{k+1})$), and connection to Insertion Sort ($O(n^2)$).
- `Amort.Recurrence.Halving`: Halving recurrence ($T(n) \le T(n/2) + c$), bit-length bound
  $T(n) \le c \cdot \text{size } n + T(1)$, and logarithmic asymptotics ($O(\log n)$).
- `Amort.Recurrence.BinarySearch`: Representative binary search comparison counting,
  halving recurrence verification, and $O(\log n)$ complexity proofs.
- `Amort.Recurrence.MasterTheorem`: Balanced divide-and-conquer master recurrence with integer
  rounding ($T(n) \le T(\lceil n/2 \rceil) + T(\lfloor n/2 \rfloor) + c \cdot n$), $O(n \log n)$
  asymptotics, and connection to Merge Sort.
- `Amort.Recurrence.DP`: State-space dynamic programming complexity framework ($|S| \cdot C$),
  2D grid DP specialization, and generic $O(|S| \cdot C)$ complexity derivations without
  requiring explicit bottom-up loops.
- `Amort.String.NaiveMatch`: Naive sliding-window string matching, character comparison counting,
  concrete worst-case comparison bound $\le (n - m + 1) \cdot m \le n \cdot m$, and substring
  occurrence correctness.
- `Amort.String.KMP`: Knuth-Morris-Pratt string matching, failure function $\pi$, preprocessing
  bound $\le 2m$, potential function analysis on index $j$ proving scanning bound $\le 2n$,
  combined linear bound $\le 2(n + m)$, and equivalence to naive matching.
- `Amort.String.LCS`: Longest Common Subsequence recursive formulation, constructive maximal
  common subsequence witness, bottom-up $(n + 1) \times (m + 1)$ dynamic programming table,
  and concrete operational step bound $\le (n + 1) \cdot (m + 1)$ ($O(n \cdot m)$).
- `Amort.String.EditDistance`: Levenshtein edit distance recursive formulation, explicit alignment
  operations, minimal-cost alignment correctness proof, bottom-up $(n + 1) \times (m + 1)$
  dynamic programming matrix, and concrete step bound $\le (n + 1) \cdot (m + 1)$ ($O(n \cdot m)$).
- `Amort.String.Asymptotics`: Bridges connecting concrete 2D table bounds to
  `Amort.Recurrence.Composition` (`isBigO_nested_loops_nat`), linear KMP bounds to
  `isBigO_sequential_add_nat`, and proving formal $O(n \cdot m)$ and $O(n + m)$ `IsBigO` bounds
  under `Filter.atTop` on $\mathbb{N} \times \mathbb{N}$.
- `Amort.String.Trie`: Prefix trie dictionary, explicit root, child transitions, word termination
  markers, retrieval soundness, and $O(\sum |P_i|)$ construction bound.
- `Amort.String.AhoCorasick`: Aho-Corasick multi-pattern matching automaton, failure links,
  depth potential function $\Phi(u) = \text{depth}(u)$, linear scanning $\le 2|T|$, and
  $O(\sum |P_i| + |T| + z)$ search.
- `Amort.String.ZAlgorithm`: Gusfield's Z-Algorithm, $Z$-array, rightmost match window $[l, r]$,
  linear comparison bound $\le 2|S|$ via window progress, and reduction $Z(P \$ T)$.
- `Amort.String.RabinKarp`: Rabin-Karp polynomial rolling hash, $O(1)$ sliding window update
  identity, hash congruence soundness, and average-case $O(|T| + |P|)$ search complexity.
- `Amort.String.SuffixArray`: Suffix array permutations and ranks, Kasai's height decrement
  invariant $h_{i+1} \ge h_i - 1$, and telescoping linear comparison bound $\le 2n$ ($O(n)$).
- `Amort.String.AdvancedAsymptotics`: Bridges connecting Trie ($O(\sum |P_i|)$), Aho-Corasick
  ($O(\sum |P_i| + |T| + z)$), Z-Algorithm ($O(|S|)$), Rabin-Karp ($O(|T| + |P|)$), and
  Kasai's LCP ($O(n)$) to Mathlib's `Asymptotics.IsBigO` under `Filter.atTop`.
- `Amort.DP.MatrixChain`: Matrix Chain Multiplication interval DP model, Bellman recurrence,
  interval state space cardinality $n(n+1)/2 \le n^2$, and $O(n^3)$ operational bound
  via `Amort.Recurrence.DP`.
- `Amort.DP.Knapsack`: 0/1 Knapsack problem Bellman recurrence, mathematical correctness
  against subcollections (soundness, completeness, optimality), and $O(n \cdot W)$ bound
  via `Amort.Recurrence.GridDP`.
- `Amort.DP.LIS`: Longest Increasing Subsequence strictly increasing sublist characterization,
  mathematical correctness proof, and $O(n^2)$ state-space model on $\text{Fin } n$
  examining predecessors $j < i$.
- `Amort.DP.Asymptotics`: Bridges connecting Matrix Chain ($O(n^3)$), 0/1 Knapsack ($O(n \cdot W)$),
  and LIS ($O(n^2)$) operational step bounds to Mathlib's `Asymptotics.IsBigO`
  under `Filter.atTop`.
- `Amort.Graph.FloydWarshall`: Floyd-Warshall all-pairs shortest paths algorithm,
  3D state space `Fin (n + 1) × Fin n × Fin n` of cardinality $(n + 1) \cdot n^2$,
  and $O(n^3)$ operational bound via `Amort.Recurrence.DP` (`DPModel`).
- `Amort.Graph.BellmanFord`: Bellman-Ford single-source shortest paths algorithm,
  $(n - 1)$ edge relaxation passes, step counter $(n - 1) \cdot |E| \le n \cdot |E|$,
  and loop product composition.
- `Amort.Graph.Traversal`: Directed graph adjacency representation, directed Handshaking Lemma
  $\sum_{v} \text{outdeg}(v) = |E|$, queue-based BFS work bound $|V| + |E|$, and unweighted
  shortest-path distance correctness.
- `Amort.Graph.TopologicalSort`: Kahn's in-degree zero queue algorithm, $O(|V| + |E|)$ step bound,
  and mathematical correctness proving DAG acyclicity.
- `Amort.Graph.DSU`: Disjoint Set Union with union-by-rank, exponential subtree size invariant
  $2^{\text{rank}} \le n$, logarithmic depth and find bounds, and $O((n + m) \log n)$ complexity.
- `Amort.Graph.Kruskal`: Kruskal's Minimum Spanning Tree algorithm, edge sorting via
  `Amort.Sorting.MergeSort`, DSU cycle checking, $O(|E| \log |V|)$ complexity, and Cut-Property
  greedy optimality.
- `Amort.Graph.Asymptotics`: Bridges connecting Floyd-Warshall ($O(n^3)$), Bellman-Ford
  ($O(|V| \cdot |E|)$), BFS ($O(|V| + |E|)$), Topological Sort ($O(|V| + |E|)$), DSU
  ($O((n + m) \log n)$), and Kruskal ($O(|E| \log |V|)$) to Mathlib `IsBigO` under `Filter.atTop`.
- `Amort.Graph.PathCompressionOnly`: Minimal DSU with path compression only (no ranks/sizes),
  iterative two-pass compression, depth-one star post-condition, linear chain $\Omega(n)$
  depth, $\Omega(n \log n)$ adversarial lower bound, and $O((n + m) \log n)$ amortized bound.
- `Amort.Graph.Dijkstra`: Dijkstra's algorithm for directed graphs with non-negative edge weights,
  greedy choice invariant, and operational step bound $(|V| + |E|) \cdot \text{Nat.size } |V|$.
- `Amort.Graph.MaxFlow`: Flow networks, capacity constraints, flow conservation, $s$-$t$ cuts,
  Cut-Flow Identity, Weak Duality, Max-Flow Min-Cut Theorem, and Edmonds-Karp $O(|V| \cdot |E|^2)$.
- `Amort.Graph.SCC`: Directed reachability, mutual reachability equivalence classes, strongly
  connected components, acyclic condensation DAG, and Kosaraju's algorithm $O(|V| + |E|)$.
- `Amort.Graph.Eulerian`: In-degree Handshaking equality, degree balance conditions, trail
  continuity, Hierholzer's cycle splicing algorithm, and linear operational bound $O(|V| + |E|)$.
- `Amort.Graph.Prim`: Prim's Minimum Spanning Tree algorithm, priority queue frontier selection,
  Cut-Property invariant, $O(|E| \log |V|)$ complexity, and comparison with Kruskal's algorithm.
- `Amort.Graph.AdvancedAsymptotics`: Bridges connecting Dijkstra ($O((|V| + |E|) \log |V|)$),
  Edmonds-Karp ($O(|V| \cdot |E|^2)$), Kosaraju ($O(|V| + |E|)$), Hierholzer ($O(|V| + |E|)$),
  and Prim ($O(|E| \log |V|)$) to Mathlib's `Asymptotics.IsBigO` framework under `Filter.atTop`.
- `Amort.DataStructure.BinaryHeap`: Binary heaps, min-heap order invariant, logarithmic height,
  sift-down and sift-up step bounds, linear build-heap theorem $\sum (n/2^h) h \le 2n$,
  and heapsort comparison complexity $O(n \log n)$.
- `Amort.DataStructure.OnlineMedian`: Dual-heap streaming model (max-heap + min-heap),
  balance invariant $|size(low) - size(high)| \le 1$,
  partition invariant $\max(low) \le \min(high)$,
  mathematical median soundness, $O(1)$ query time, and $O(\log n)$ insertion/rebalance time.
- `Amort.DataStructure.BalancedBST`: Height-balanced binary search trees with size annotations,
  $O(1)$ tree rotations preserving BST ordering and size, and $O(\log n)$ online order-statistic
  queries (`rank`, `select`, `find`, `insert`).
- `Amort.DataStructure.DynamicArray`: Dynamic array with capacity doubling, potential function
  $\Phi = 2n - C$, amortized $O(1)$ push ($T_{\text{amortized}} \le 3$), non-negativity,
  and $O(k)$ total actual cost bound across $k$ pushes.
- `Amort.DataStructure.TwoStackQueue`: Two-stack FIFO queue backed by input and output stacks,
  potential function $\Phi = 2 \cdot |\text{inStack}|$, amortized $O(1)$ operations
  ($T_{\text{amortized}} \le 3$), FIFO correctness, and $O(m)$ total actual cost bound.
- `Amort.DataStructure.Asymptotics`: Bridges connecting operational and amortized bounds
  for heaps, online median, balanced BSTs, dynamic arrays, and two-stack queues to Mathlib's
  `Asymptotics.IsBigO` framework under `Filter.atTop`.
- `Amort.Greedy.IntervalScheduling`: Interval representation with positive duration, compatibility
- `Amort.Greedy.IntervalScheduling`: Interval representation with positive duration, compatibility
  predicates, greedy earliest-finish-time selection, exchange argument optimality theorem,
  and $O(n \log n)$ operational step bound dominated by sorting.
- `Amort.Greedy.Huffman`: Alphabet symbols with positive weights, prefix tree representation,
  external path length equivalence, greedy choice property for minimal-weight siblings, and
  $O(n \log n)$ priority queue construction bound.
- `Amort.Greedy.MedianOfMedians`: Groups of 5, group medians, median-of-medians pivot
  quality theorem (at least $3n/10 - 6$ elements), branch bound $\le 7n/10 + 6$,
  and $O(n)$ linear-time divide-and-conquer recurrence.
- `Amort.Greedy.Asymptotics`: Bridges connecting Interval Scheduling ($O(n \log n)$),
  Huffman ($O(n \log n)$), and Median-of-Medians ($O(n)$) to Mathlib `IsBigO` under `Filter.atTop`.
- `Amort.Geometry.ConvexHull`: 2D point representation, orientation determinant cross product,
  monotone chain stack construction, amortized scanning bound $\le 2n$ stack operations, and
  $O(n \log n)$ total operational bound.
- `Amort.Geometry.ClosestPair`: Squared Euclidean distance, divide-and-conquer splitting by
  median $x$, strip geometric sparsity lemma ($\le 4$ points per cell, $\le 7$ neighbors),
  and $O(n \log n)$ divide-and-conquer recurrence.
- `Amort.Geometry.Asymptotics`: Bridges connecting 2D Convex Hull ($O(n \log n)$) and Closest Pair
  ($O(n \log n)$) to Mathlib `IsBigO` under `Filter.atTop`.
- `Amort.NumberTheory.ModExp`: Repeated squaring binary exponentiation ($a^b \bmod m$),
  loop state correctness invariant, and multiplication bound $\le 2 \cdot \text{size } b$
  ($O(\log b)$).
- `Amort.NumberTheory.ExtendedGCD`: Extended Euclidean algorithm computing Bézout coefficients,
  linear combination invariants, remainder halving $2 \cdot r_{k+2} < r_k$, and logarithmic
  step bound $\le 2 \cdot \text{size}(\min a\ b) + 1$ ($O(\log(\min a\ b))$).
- `Amort.NumberTheory.Sieve`: Sieve of Eratosthenes composite marking model, correctness
  theorem ($k$ unmarked iff prime), and harmonic operational work bound $O(n \log n)$.
- `Amort.NumberTheory.Asymptotics`: Bridges connecting ModExp ($O(\log b)$), Extended GCD
  ($O(\log(\min a\ b))$), and Sieve ($O(n \log n)$) to Mathlib `IsBigO` under `Filter.atTop`.
- `Amort.Algebraic.FFT`: Fast Fourier Transform, roots of unity, cancellation lemma,
  Cooley-Tukey Radix-2 decomposition $A(x) = A_{even}(x^2) + x A_{odd}(x^2)$, butterfly
  correctness, divide-and-conquer recurrence $T(n) \le 2T(n/2) + c \cdot n$, and $O(n \log n)$
  polynomial multiplication complexity.
- `Amort.Algebraic.Strassen`: Strassen's sub-cubic matrix multiplication, $2 \times 2$ block
  matrices, 7 auxiliary multiplications, algebraic equivalence theorem in arbitrary rings,
  divide-and-conquer recurrence $T(n) \le 7T(n/2) + c \cdot n^2$, and $O(n^{\log_2 7})$ bound.
- `Amort.Algebraic.Asymptotics`: Bridges connecting FFT ($O(n \log n)$), polynomial multiplication
  ($O(n \log n)$), and Strassen's matrix multiplication ($O(n^{\log_2 7})$) to Mathlib `IsBigO`
  under `Filter.atTop`, with rigorous proof that $\log_2 7 < 3$.
- `Amort.Complexity.Classes`: Complexity classes P and NP, polynomial-time verifiers,
  polynomial certificate relations, embedding $P \subseteq NP$, polynomial-time many-one (Karp)
  reductions with transitivity, and NP-hardness and NP-completeness.
- `Amort.Complexity.TwoSAT`: 2-CNF boolean formulas, implication digraph, contrapositive
  path symmetry, connection to `Amort.Graph.SCC`, soundness and completeness theorem
  (satisfiable $\iff$ no variable $x$ lies in the same SCC as $\neg x$), and linear operational
  step bound $O(|V| + |E|) = O(n + m)$.
- `Amort.Complexity.KarpReductions`: Formalization of 3-SAT, Independent Set, Vertex Cover, and
  Clique, Complement Duality theorem ($S \text{ IS} \iff S^c \text{ VC} \iff S \text{ Clique in }
  \overline{G}$), 3-SAT to Independent Set clause gadget reduction soundness and completeness,
  and reduction chain $\text{3-SAT} \le_P \text{Independent Set} \le_P \text{Vertex Cover}
  \le_P \text{Clique}$.
- `Amort.Complexity.Asymptotics`: Bridges connecting 2-SAT linear time, canonical polynomial
  growth, 3-SAT gadget graph size ($O(m)$ vertices, $O(m^2)$ edges), and complement graph edge
  complexity to Mathlib's `Asymptotics.IsBigO` framework under `Filter.atTop`.
- `Amort.Approximation.VertexCover`: 2-approximation for vertex cover via maximal matching,
  lower bound $|M| \le |C^*|$, approximation ratio $|C| \le 2|C^*|$, and linear time $O(|V| + |E|)$.
- `Amort.Approximation.MetricTSP`: 2-approximation for metric TSP via MST double-tree walk,
  triangle inequality, shortcutting theorem, and bound $\text{cost} \le 2 \cdot \text{OPT}$.
- `Amort.Approximation.SetCover`: Greedy $H(n)$-approximation for set cover, harmonic numbers,
  marginal charging scheme, and bound $|\mathcal{C}_{\text{greedy}}| \le H(n) \cdot \text{OPT}$.
- `Amort.Approximation.Asymptotics`: Bridges connecting Vertex Cover ($O(|V| + |E|)$), Metric TSP
  ($O(n^2 \log n)$), and Set Cover ($O(m \cdot n)$) to Mathlib `IsBigO` under `Filter.atTop`.
- `Amort.Graph.Advanced.HopcroftKarp`: Maximum bipartite matching, alternating/augmenting paths,
  strictly increasing path lengths, phase bound $\le 2\sqrt{|V|}$, and $O(|E|\sqrt{|V|})$ time.
- `Amort.Graph.Advanced.HallMarriage`: Hall's Marriage Theorem, neighborhood $N(S)$, combinatorial
  condition $|S| \le |N(S)|$, max-flow reduction, and equivalence with saturating matchings.
- `Amort.Graph.Advanced.BridgeTarjan`: Tarjan's DFS bridge and articulation point finding, low-link,
  bridge characterization $\text{low}[v] > \text{disc}[u]$, and $O(|V| + |E|)$ bound.
- `Amort.Graph.Advanced.Asymptotics`: Bridges connecting Hopcroft-Karp and Tarjan bridge-finding
  to Mathlib `IsBigO` under `Filter.atTop`.
- `Amort.Randomized.Quicksort`: Expected complexity of randomized quicksort, comparison indicator
  variables $X_{ij}$, pivot probability $2/(j - i + 1)$, and $O(n \log n)$ harmonic bound.
- `Amort.Randomized.KargerMinCut`: Karger's random contraction algorithm for global min-cut,
  degree bound $|E| \ge n k / 2$, survival $(n-2)/n$, telescoping lower bound $2/(n(n-1))$,
  and repetition amplification.
- `Amort.Randomized.UniversalHash`: 2-Universal hash families, collision bound $\le 1/m$,
  $O(1)$ expected lookup, and reservoir sampling streaming invariant $k/(t+1)$.
- `Amort.Randomized.Asymptotics`: Bridges connecting Expected Quicksort ($O(n \log n)$),
  Karger Min-Cut ($O(n^4)$), and Universal Hashing ($O(1)$) to Mathlib `IsBigO`.
- `Amort.LP.Duality`: Linear Programming standard inequality form, primal and dual feasibility,
  Weak Duality Theorem $c^T x \le b^T y$, Optimality Certificate Theorem ($c^T x^* = b^T y^*$),
  and unboundedness infeasibility corollaries.
- `Amort.LP.Simplex`: Simplex slack form, dictionary representation $x_B = \bar{b} - \bar{A} x_N$,
  basic solution feasibility invariant $\bar{b} \ge 0$, ratio test, pivot preservation,
  and objective progression.
- `Amort.LP.Asymptotics`: Bridges connecting simplex pivot step ($O(m \cdot n)$) and LP feasibility
  verification to Mathlib `IsBigO` under `Filter.atTop`.
- `Amort.Graph.Ackermann.AckermannHierarchy`: Standard Ackermann hierarchy $A_k(n)$, strict
  monotonicity, milestone evaluations up to $A(4, 1) = 65533$, functional inverse Ackermann
  function $\alpha(n)$, and slow-growth bound $\alpha(n) \le 4$ for all practical $n$.
- `Amort.Graph.Ackermann.PathCompression`: DSU with path compression during `find`, strict parent
  rank hierarchy preservation, and logarithmic rank bound $\text{rank}(v) \le \log_2 n$.
- `Amort.Graph.Ackermann.PotentialBound`: Rank level intervals $[A_k(r), A_{k+1}(r)]$, potential
  function analysis, telescoping amortized summation theorem, and $O(m \cdot \alpha(n))$ bound.
- `Amort.Graph.Ackermann.Asymptotics`: Bridges connecting DSU total work to Mathlib `IsBigO` under
  `Filter.atTop`.
- `Amort.String.SuffixTree.CompactTree`: Compact suffix trees with slice intervals $[l, r]$,
  internal branching degree $\ge 2$, leaf bound $\le n$, internal node bound $\le n - 1$, and
  total node bound $\le 2n$.
- `Amort.String.SuffixTree.SuffixLink`: Suffix links mapping $a \beta$ to $\beta$, depth invariant
  $\text{stringDepth}(\text{link}(u)) = \text{stringDepth}(u) - 1$, and chain termination.
- `Amort.String.SuffixTree.Ukkonen`: Ukkonen's online active point, three extension rules, global
  end pointer $O(1)$ amortized leaf extensions, split bounds $\le n$, and $O(n)$ linear time.
- `Amort.String.SuffixTree.Asymptotics`: Bridges connecting Ukkonen linear time to Mathlib `IsBigO`
  under `Filter.atTop`.
- `Amort.Distributed.Causality`: Distributed events, Lamport's happens-before strict partial order,
  Lamport scalar clock consistency, and Vector Clock causal isomorphism:
  $V(e_1) < V(e_2) \iff e_1 \to e_2$.
- `Amort.Distributed.Impossibility`: Gilbert-Lynch CAP impossibility theorem (linearizability and
  availability cannot both hold across partitions) and Two Generals' impossibility of agreement.
- `Amort.Distributed.Consensus`: Majority quorum intersection lemma, Single-Decree Paxos (Synod)
  core invariant, learner agreement ($v_1 = v_2$), Multi-Paxos replicated log, and Raft invariants.
- `Amort.Distributed.BFT`: Byzantine fault tolerance ($3f + 1$), PBFT quorum math,
  Lamport-Shostak-Pease $N \le 3f$ impossibility, and Oral Messages $OM(m)$ validity and agreement.
- `Amort.Distributed.Snapshot`: Chandy-Lamport distributed snapshot algorithm, FIFO marker
  discipline, and consistent cut global state theorem.
-/
