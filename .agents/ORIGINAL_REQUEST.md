# Original User Request

## 2026-09-07T18:31:02Z

Formalize binary GCD (Stein's algorithm) in Lean 4, prove termination, verify mathematical equivalence against `Nat.gcd`, formalize step bounds, and document the work.

Working directory: /home/deck/projects/amort
Integrity mode: demo

## Requirements

### R1. Formal Definition and Termination
Define the binary GCD algorithm in Lean 4 over natural numbers with provable termination based on argument size/sum.

### R2. Mathematical Equivalence with Nat.gcd
Prove that the binary GCD implementation is mathematically equivalent to `Nat.gcd`:
`∀ (a b : ℕ), binaryGcd a b = Nat.gcd a b`
Structure the proof cleanly using auxiliary lemmas for parity, factor-of-two elimination, and subtraction invariants, reusing Mathlib where appropriate without verbatim copying.

### R3. Step Counting & Bound
Define companion step-counting or an instrumented representation that counts recursive transitions, establishing an explicit upper bound on step count in terms of bit length / logarithmic size.

### R4. Build & Verification Integrity
Ensure the repository compiles cleanly with `lake build` without unresolved `sorry`s in the final theorems.

### R5. Documentation
Provide clear markdown documentation explaining the architecture of the formalization, the DAG of invariant lemmas, and proof notes for future reuse/upstream contribution.

## Acceptance Criteria

### Verification
- [ ] Running `lake build` in `/home/deck/projects/amort` succeeds with 0 errors and 0 warnings.
- [ ] `#print axioms` on the main correctness theorem confirms it does not rely on `sorryAx`.
- [ ] Equivalence with `Nat.gcd` is proven for all `a, b : ℕ`.
- [ ] Step count definition and upper bound theorem are proven.
- [ ] Documentation file exists and describes the implementation and invariant lemma structure.

## 2026-09-07T21:01:05Z

Connect Binary GCD complexity bounds to Mathlib's `Asymptotics.IsBigO`, formalize step counting for standard Euclidean GCD with a logarithmic upper bound, and conduct a dedicated style guide audit for full Mathlib readiness.

Working directory: /home/deck/projects/amort
Integrity mode: demo

## Requirements

### R1. Formalize Standard Euclidean GCD Step Counting & Upper Bound
Define the step counter `euclideanGcdSteps (a b : ℕ) : ℕ` mirroring `Nat.gcd a b`. Prove provable termination and establish an upper bound showing `euclideanGcdSteps a b ≤ 2 * Nat.size (min a b) + 1` (or in terms of `size (a + b)`), formalizing the halving property of modulo ($a \bmod b < a / 2$ when $b \le a$).

### R2. Asymptotics Bridge to Mathlib `IsBigO`
Connect the proven step bounds for Binary GCD to Mathlib's `Asymptotics.IsBigO` under the `atTop` filter on the combined input measure (or size of $a + b$ / $\min(a, b)$), providing idiomatic asymptotic complexity theorems.

### R3. Style Guide & Linter Audit
Ensure all new and updated code strictly adheres to Mathlib conventions:
- Scoped under `namespace Nat` (or appropriate sub-namespace).
- Uses `lemma` for auxiliaries and `theorem` for milestones.
- Docstrings formatted as `/-- ... -/` without assignment metadata tags.
- Line length ≤ 100 characters.
- Zero `sorryAx` or non-standard axioms verified via `#print axioms`.

### R4. Build & Documentation
The repository must build cleanly with `lake build` (0 warnings, 0 errors). Provide clear documentation explaining the module structure, theorem statements, and asymptotic definitions.

## Acceptance Criteria

### Verification
- [ ] Running `lake build` in `/home/deck/projects/amort` succeeds with 0 errors and 0 warnings.
- [ ] `#print axioms` on the main asymptotic and Euclidean step bound theorems confirms zero `sorryAx`.
- [ ] `euclideanGcdSteps` is defined, terminates, and its logarithmic upper bound is formally proven.
- [ ] `IsBigO` connection theorem is proven using Mathlib's asymptotics library.
- [ ] Code passes style check guidelines (proper namespacing, docstrings, line lengths).
- [ ] Documentation file exists and describes the new formalizations.

## 2026-09-07T21:52:08Z

Formalize comparison counting and time complexity for Insertion Sort ($O(n^2)$) and Merge Sort ($O(n \log n)$) in Lean 4, reusing Mathlib's sorting definitions and connecting to `Asymptotics.IsBigO`.

Working directory: /home/deck/projects/amort
Integrity mode: demo

## Requirements

### R1. Insertion Sort Comparison Counting & O(n²) Upper Bound
Model comparison counting for insertion sort over lists, proving equivalence to Mathlib's `List.insertionSort`. Prove the concrete comparison upper bound $\le \frac{n(n-1)}{2} \le n^2$ where $n = l.\text{length}$, and connect it to Mathlib's `IsBigO` under `Filter.atTop` on list length.

### R2. Merge Sort Comparison Counting & O(n log n) Upper Bound
Model comparison counting for merge sort over lists, proving equivalence to Mathlib's `List.mergeSort` (or standard functional merge sort). Prove the concrete comparison upper bound $\le n \cdot \text{Nat.size } n$, and connect it to Mathlib's `IsBigO` under `Filter.atTop` on list length.

### R3. Style Guide & Axiom Integrity
Ensure all definitions and theorems adhere to Mathlib conventions (scoped under appropriate namespaces such as `List`, line lengths $\le 100$, docstrings `/-- ... -/`, zero `sorryAx` confirmed via `#print axioms`).

### R4. Build & Documentation
The project must compile cleanly with `lake build` (0 warnings, 0 errors). Provide clear documentation explaining the comparison models, recurrences, and asymptotic connections in `Amort/Sorting/Sorting.md`.

## Acceptance Criteria

### Verification
- [ ] `lake build` succeeds in `/home/deck/projects/amort` with 0 errors and 0 warnings.
- [ ] `#print axioms` on the main sorting complexity and `IsBigO` theorems confirms zero `sorryAx`.
- [ ] Equivalence of instrumented/counted sorting to Mathlib's sorted outputs is formally proven.
- [ ] The $O(n^2)$ bound for insertion sort and $O(n \log n)$ bound for merge sort are formally proven.
- [ ] Documentation explains the recurrence relations, bounds, and asymptotic proofs.

## 2026-09-16T03:21:17Z

Formalize the information-theoretic lower bound for comparison-based sorting ($\Omega(n \log n)$) in Lean 4 within the `Amort.Sorting` namespace.

Working directory: /workspace/amort
Integrity mode: development

## Requirements

### R1. Decision Tree Model
Formalize an abstract binary decision tree for comparison-based algorithms (evaluating comparisons between elements of a finite collection or indices `Fin n`). Define the depth (height / worst-case query count) and leaf count of the tree, and prove by structural induction that any decision tree $T$ satisfies:
$$\text{leafCount}(T) \le 2^{\text{depth}(T)}$$

### R2. Permutation Coverage & Factorial Bound
Formalize the requirement that any correct comparison-based sorting algorithm on $n$ elements must be able to output or distinguish all $n!$ possible permutations of the input. Establish that the number of reachable leaves of a correct sorting tree for $n$ elements is at least $n!$:
$$n! \le \text{leafCount}(T) \le 2^{\text{depth}(T)}$$
Deduce the worst-case lower bound:
$$\text{depth}(T) \ge \lceil \log_2(n!) \rceil \quad (\text{or in Lean, } \text{Nat.clog } 2\ (n!) \le \text{depth}(T))$$

### R3. Factorial Combinatorial and Asymptotic Bounds
Prove the combinatorial lower bound on factorial growth (e.g. $n! \ge (n/2)^{n/2}$ or $2^k \ge n! \implies k = \Omega(n \log n)$). Connect this lower bound to Mathlib's asymptotic complexity framework (`Mathlib.Analysis.Asymptotics.IsBigO` / `IsTheta`), proving that $\log(n!) = \Omega(n \log n)$ (i.e. $n \log n = O(\log(n!))$ under `Filter.atTop`).

### R4. Library Integration
Integrate the new formalization modules under `Amort/Sorting/` (e.g. `Amort/Sorting/DecisionTree.lean`, `Amort/Sorting/LowerBound.lean`), expose them in `Amort.lean`, and document the mathematical architecture in `Amort/Sorting/Sorting.md`.

## Acceptance Criteria

### Correctness and Build
- [ ] The entire project builds with `lake build` with 0 errors and 0 warnings.
- [ ] No theorems rely on `sorry` or `sorryAx` (all proofs are fully checked using standard Lean 4 axioms).
- [ ] `leafCount T ≤ 2 ^ depth T` is formalized and proven.
- [ ] `Nat.factorial n ≤ 2 ^ depth T` (or equivalent for correct sorters) is formalized and proven.
- [ ] Concrete and asymptotic lower bounds ($\text{depth} \ge \text{clog}_2(n!)$ and $\Omega(n \log n)$) are stated and proven.
- [ ] All new files are exported in `Amort.lean` and documented in `Amort/Sorting/Sorting.md`.

## 2026-09-17T04:09:19Z

Formalize algorithmic recurrence and complexity theorems (compositional loop algebra, telescoping loops, halving/binary search, and divide-and-conquer master recurrences) in Lean 4 within `Amort.Recurrence`.

Working directory: /workspace/amort
Integrity mode: development

## Requirements

### R1. Compositional Complexity Algebra
Formalize high-level algorithmic composition theorems connecting to Mathlib's `Mathlib.Analysis.Asymptotics.IsBigO`:
- Nested loops: if an outer loop executes $N(n) = O(g_1(n))$ iterations and each iteration costs $C(n) = O(g_2(n))$, the combined cost is $O(g_1(n) \cdot g_2(n))$.
- Sequential phases: running step 1 with $O(g_1(n))$ followed by step 2 with $O(g_2(n))$ yields $O(g_1(n) + g_2(n))$ (or $O(\max(g_1, g_2))$).

### R2. Linear & Telescoping Recurrences
Formalize general recurrence theorems for loop algorithms where $T(n+1) \le T(n) + f(n)$:
- General power step: if $T(n+1) \le T(n) + c \cdot n^k$, then $T(n) = O(n^{k+1})$ under `Filter.atTop`.
- Constant step: if $T(n+1) \le T(n) + c$, then $T(n) = O(n)$.
- Connect to iterative sorting (e.g. Insertion Sort step bound yielding $O(n^2)$ by mapping to the $k=1$ recurrence).

### R3. Halving & Binary Search Recurrences
Formalize recurrence bounds for decrease-by-constant-factor algorithms:
- Halving recurrence: if $T(n) \le T(n / 2) + c$ for $n \ge 2$, then $T(n) \le c \cdot \text{Nat.size } n + T(1)$ and $T(n) = O(\text{Nat.size } n)$ / $O(\log n)$ under `Filter.atTop`.
- Formalize a representative binary search step counter on a range or list of size $n$, proving its comparison count satisfies this halving recurrence and is $O(\log n)$.

### R4. Divide-and-Conquer Recurrences
Formalize the standard balanced divide-and-conquer recurrence with integer rounding:
- If $T(n) \le T((n + 1) / 2) + T(n / 2) + c \cdot n$ for $n \ge 2$, then $T(n) = O(n \cdot \text{Nat.size } n)$ / $O(n \log n)$ under `Filter.atTop`.
- Connect to divide-and-conquer sorting (e.g. Merge Sort step bound yielding $O(n \log n)$ by mapping to this recurrence).

### R5. Library Integration & Documentation
Integrate the modules under `Amort/Recurrence/` (e.g. `Composition.lean`, `Telescoping.lean`, `Halving.lean`, `MasterTheorem.lean`, `BinarySearch.lean`), export them in `Amort.lean`, and document the mathematical architecture in `Amort/Recurrence/Recurrence.md` and `README.md`.

## Acceptance Criteria

### Correctness and Build
- [ ] The entire project builds cleanly with `lake build` (0 errors, 0 warnings).
- [ ] No theorems rely on `sorry` or `sorryAx` (all proofs rely strictly on standard Lean 4 foundational axioms).
- [ ] Composition theorems for loop products ($O(g_1) \times O(g_2) \implies O(g_1 \cdot g_2)$) and sums are proven.
- [ ] Telescoping recurrence theorem ($T(n+1) \le T(n) + c \cdot n^k \implies O(n^{k+1})$) is proven.
- [ ] Halving recurrence theorem ($T(n) \le T(n/2) + c \implies O(\log n)$) and binary search complexity are proven.
- [ ] Divide-and-conquer recurrence theorem ($T(n) \le T(\lceil n/2 \rceil) + T(\lfloor n/2 \rfloor) + c \cdot n \implies O(n \log n)$) is proven.
- [ ] All new modules are exported in `Amort.lean` and documented in `Amort/Recurrence/Recurrence.md`.

## 2026-09-17T04:55:59Z

Formalize standard textbook string algorithms in Lean 4 within `Amort.String`, contrasting naive solutions with optimal algorithms: String Matching (Naive $O(n \cdot m)$ vs. KMP $O(n + m)$) and Sequence Alignment (LCS and Edit Distance $O(n \cdot m)$ DP), proving correctness, step bounds, and asymptotic complexity.

Working directory: /workspace/amort
Integrity mode: development

## Requirements

### R1. String Matching: Naive vs. Knuth-Morris-Pratt (KMP)
- **Naive String Matching**:
  - Formalize the sliding-window character comparison algorithm checking pattern $P$ (length $m$) at each shift $s \in [0, n - m]$ in text $T$ (length $n$).
  - Step counter proving worst-case comparison bound $\le (n - m + 1) \cdot m \le n \cdot m$ ($O(n \cdot m)$).
- **Knuth-Morris-Pratt (KMP)**:
  - Formalize the prefix/failure function $\pi$ with preprocessing bound $\le 2m$ character steps.
  - Formalize KMP text scanning with potential function analysis on pattern index $j$, proving search executes in $\le 2n$ character comparisons/transitions.
  - Combined step bound $\le 2(n + m)$ ($O(n + m)$ linear time).
- **Equivalence & Correctness**:
  - Prove that Naive matching and KMP produce identical match indices, and that reported positions correspond exactly to occurrences of $P$ as a substring in $T$.

### R2. Sequence Alignment: Dynamic Programming (LCS & Edit Distance)
- **Longest Common Subsequence (LCS)**:
  - Formalize the standard recursive formulation and bottom-up $(n+1) \times (m+1)$ dynamic programming table.
  - Prove mathematical correctness (computing the maximum length common subsequence).
  - Step counter proving the DP table is computed in $\le (n + 1) \cdot (m + 1)$ operations ($O(n \cdot m)$).
- **Edit Distance (Levenshtein Distance)**:
  - Formalize recursive edit distance with operations (insertion, deletion, substitution).
  - Formalize the 2D DP matrix computation, proving step count $\le (n + 1) \cdot (m + 1)$ ($O(n \cdot m)$).
  - Correctness: the DP matrix computes the minimal cost alignment between two sequences.

### R3. Asymptotics & Composition Bridges
- Connect $O(n \cdot m)$ 2D table / nested loop bounds to `Amort.Recurrence.Composition` (`isBigO_nested_loops_nat`).
- Connect $O(n + m)$ linear KMP bound to `Amort.Recurrence.Composition` (`isBigO_sequential_add_nat`).
- Under `Filter.atTop` on $\mathbb{N} \times \mathbb{N}$, verify formal `Asymptotics.IsBigO` bounds for all four algorithms.

### R4. Library Integration & Documentation
- Implement clean modules under `Amort/String/`:
  - `Amort/String/NaiveMatch.lean`
  - `Amort/String/KMP.lean`
  - `Amort/String/LCS.lean`
  - `Amort/String/EditDistance.lean`
  - `Amort/String/Asymptotics.lean`
- Re-export all modules in `Amort.lean`.
- Document mathematical architecture, invariant lemmas, potential functions, and comparison tables in `Amort/String/String.md` and `README.md`.

## Acceptance Criteria

### Correctness and Build
- [ ] The entire project builds cleanly with `lake build` (0 errors, 0 warnings).
- [ ] No theorems rely on `sorry` or `sorryAx` (strictly foundational Lean 4 axioms).
- [ ] Naive string matcher ($O(n \cdot m)$) and KMP ($O(n + m)$) are proven equivalent and correct.
- [ ] LCS ($O(n \cdot m)$) and Edit Distance ($O(n \cdot m)$) DP algorithms are proven correct with concrete step bounds.
- [ ] All bounds are connected to Mathlib `Asymptotics.IsBigO` via `Amort.Recurrence.Composition`.
- [ ] All new files are exported in `Amort.lean` and documented in `Amort/String/String.md`.

## 2026-09-18T02:45:46Z

Formalize textbook dynamic programming algorithms (Interval DP: Matrix Chain Multiplication $O(n^3)$, Grid DP: 0/1 Knapsack $O(n \cdot W)$, and Longest Increasing Subsequence $O(n^2)$) in Lean 4 within `Amort.DP`, leveraging the `Amort.Recurrence.DP` state-space complexity framework and proving mathematical correctness, operational step bounds, and asymptotic complexity in Mathlib `IsBigO`.

Working directory: /workspace/amort
Integrity mode: development

## Requirements

### R1. Interval DP: Matrix Chain Multiplication
- Formalize matrix dimensions for a chain of $n$ matrices as a list/vector of lengths $p_0, p_1, \dots, p_n$.
- Define the recursive Bellman cost function $M(i, j)$ representing the minimum number of scalar multiplications needed to compute $A_i \dots A_j$:
  $$M(i, i) = 0, \quad M(i, j) = \min_{i \le k < j} \{ M(i, k) + M(k+1, j) + p_i \cdot p_{k+1} \cdot p_{j+1} \}$$
- Formalize the interval state space of pairs $(i, j)$ with $0 \le i \le j < n$, establishing that the state space cardinality is $n(n+1)/2 \le n^2$.
- Model the local work per interval $(i, j)$, evaluating $j - i \le n$ split choices ($c(i, j) \le n$), and prove the total operations across all states is bounded by $n^3$ via `Amort.Recurrence.DP`.

### R2. Grid DP: 0/1 Knapsack Problem
- Formalize items with weights and values ($w_i, v_i \in \mathbb{N}$), knapsack capacity $W \in \mathbb{N}$, and the standard recursive decision formulation:
  $$K(0, w) = 0, \quad K(i+1, w) = \begin{cases} K(i, w) & \text{if } w < w_i \\ \max(K(i, w), v_i + K(i, w - w_i)) & \text{if } w \ge w_i \end{cases}$$
- Prove mathematical correctness: $K(n, W)$ equals the maximum value attainable by any subcollection of items whose total weight does not exceed $W$.
- Instantiate `Amort.Recurrence.GridDP` on state space $\text{Fin}(n+1) \times \text{Fin}(W+1)$ with unit/constant local transitions ($C = 1$), proving total work is bounded by $(n+1)(W+1)$ ($O(n \cdot W)$).

### R3. Longest Increasing Subsequence (LIS)
- Formalize the predicate `IsStrictlyIncreasingSubsequence` and the recursive/subproblem characterization of LIS.
- Prove correctness: the computed value corresponds to the length of the longest strictly increasing sublist.
- Formalize the $O(n^2)$ state-space model where state $i \in \text{Fin } n$ examines predecessors $j < i$, proving total work across all states is bounded by $n(n+1)/2 \le n^2$.

### R4. Asymptotic Complexity Bridges & Module Integration
- Connect all step bounds to Mathlib's `Mathlib.Analysis.Asymptotics.IsBigO` under `Filter.atTop` (e.g. $O(n^3)$ for Matrix Chain Multiplication, $O(n \cdot W)$ for Knapsack, and $O(n^2)$ for LIS).
- Implement modular, clean Lean files under `Amort/DP/`:
  - `Amort/DP/MatrixChain.lean`
  - `Amort/DP/Knapsack.lean`
  - `Amort/DP/LIS.lean`
  - `Amort/DP/Asymptotics.lean`
- Re-export all modules in `Amort.lean`.
- Document mathematical architecture, invariant hierarchies, and proof strategies in `Amort/DP/DP.md` and individual algorithm `.md` documents, updating `README.md`.

## Acceptance Criteria

### Correctness and Build
- [ ] The entire project builds cleanly with `lake build Amort` (0 errors, 0 warnings).
- [ ] Zero reliance on `sorry` or `sorryAx` (all proofs rely strictly on foundational Lean 4 axioms).
- [ ] Matrix Chain Multiplication $O(n^3)$ bound is formally proven using the interval state-space DP model.
- [ ] 0/1 Knapsack correctness and $O(n \cdot W)$ bound are formally proven using `GridDP`.
- [ ] LIS correctness and $O(n^2)$ bound are formally proven.
- [ ] All step bounds are connected to Mathlib's `IsBigO`.
- [ ] Comprehensive Markdown proof documentation is provided for each module.
- [ ] All new files are exported in `Amort.lean` and indexed in `README.md`.

## 2026-09-18T03:15:57Z

Formalize textbook graph algorithms in Lean 4 within `Amort.Graph`:
1. Graph Dynamic Programming & Shortest Paths: Floyd-Warshall ($O(|V|^3)$ via `Amort.Recurrence.DP`) and Bellman-Ford ($O(|V| \cdot |E|)$ via loop composition).
2. Foundational Linear Graph Traversals: BFS with Handshaking degree sum ($O(|V| + |E|)$) and Topological Sort (Kahn's algorithm on DAGs, $O(|V| + |E|)$).
3. Amortized Data Structures & MST: Disjoint Set Union (Union-Find) with rank bounds ($O((|V| + |E|) \log |V|)$) and Kruskal's Minimum Spanning Tree algorithm.

Working directory: /workspace/amort
Integrity mode: demo

## Requirements

### R1. Graph Dynamic Programming & Shortest Paths
- Formalize weighted directed graphs with finite vertices $\text{Fin } n$.
- **Floyd-Warshall**: Formalize all-pairs shortest paths via 3D dynamic programming $(k, i, j) \in \text{Fin}(n+1) \times \text{Fin } n \times \text{Fin } n$, proving total operations bounded by $(n+1) \cdot n^2 = O(n^3)$ using `Amort.Recurrence.DP`.
- **Bellman-Ford**: Formalize single-source shortest paths via $|V| - 1$ edge relaxation passes, proving $O(|V| \cdot |E|)$ operations via `Amort.Recurrence.Composition.isBigO_nested_loops_nat`.

### R2. Linear Graph Traversals & Handshaking Lemma ($O(|V| + |E|)$)
- Formalize adjacency list representation and the Handshaking Lemma: $\sum_{v \in V} \text{outdeg}(v) = |E|$.
- **Breadth-First Search (BFS)**: Formalize queue-based traversal visiting vertices at most once and scanning outgoing edges, proving total work bounded by $|V| + |E|$ ($O(|V| + |E|)$) and unweighted shortest-path distance correctness.
- **Topological Sort**: Formalize Kahn's in-degree zero queue algorithm, proving $O(|V| + |E|)$ step bound and topological sort correctness on DAGs.

### R3. Amortized Data Structures & Minimum Spanning Trees
- **Disjoint Set Union (Union-Find)**: Formalize union-by-rank, proving tree depth bounded by $\log_2 n$ and $m$ operations on $n$ elements bounded by $O((n + m) \log n)$.
- **Kruskal's MST Algorithm**: Formalize edge sorting (connecting to `Amort.Sorting.MergeSort`) followed by DSU cycle checking, proving overall time complexity and minimum spanning tree cut-property optimality.

### R4. Asymptotics Bridges & Module Integration
- Connect all operational bounds to Mathlib's `Mathlib.Analysis.Asymptotics.IsBigO` under `Filter.atTop`.
- Implement clean, modular Lean files under `Amort/Graph/`:
  - `Amort/Graph/FloydWarshall.lean`
  - `Amort/Graph/BellmanFord.lean`
  - `Amort/Graph/Traversal.lean`
  - `Amort/Graph/TopologicalSort.lean`
  - `Amort/Graph/DSU.lean`
  - `Amort/Graph/Kruskal.lean`
  - `Amort/Graph/Asymptotics.lean`
- Re-export all modules in `Amort.lean`.
- Document mathematical architecture, invariant hierarchies, and proof strategies in `Amort/Graph/Graph.md` and individual algorithm `.md` documents, updating `README.md`.

## Acceptance Criteria

### Correctness and Build
- [ ] The entire project builds cleanly with `lake build Amort` (0 errors, 0 warnings).
- [ ] Zero reliance on `sorry` or `sorryAx` (all proofs rely strictly on foundational Lean 4 axioms).
- [ ] Floyd-Warshall $O(|V|^3)$ bound is formally proven using `Amort.Recurrence.DP`.
- [ ] Bellman-Ford $O(|V| \cdot |E|)$ bound is formally proven using loop product composition.
- [ ] BFS and Topological Sort $O(|V| + |E|)$ bounds are formally proven using the degree sum.
- [ ] DSU and Kruskal's algorithm bounds and correctness are formally proven.
- [ ] All step bounds are connected to Mathlib `IsBigO`.
- [ ] Comprehensive Markdown proof documentation is provided for each module.
- [ ] All new modules are exported in `Amort.lean` and indexed in `README.md`.

## 2026-09-20T00:14:58Z

Formalize Disjoint Set Union with iterative path compression only (no ranks/sizes) and the complete Quicksort algorithm canon (correctness, worst-case $O(n^2)$, worst-case $O(n \log n)$ with $O(n)$ median-of-medians selection, and average-case $O(n \log n)$ with random pivot) in Lean 4.

Working directory: /workspace/amort
Integrity mode: development

## Requirements

### R1. Disjoint Set Union with Path Compression Only (Iterative & Arbitrary Linking)
- Formalize minimal DSU state containing only parent pointers (`parent : Fin n → Fin n`) without rank or size arrays.
- Formalize iterative two-pass / while-loop path compression: traverse to root, then re-point visited nodes directly to the root.
- Formalize arbitrary/naive linking: `unite(u, v)` attaches root $u$ directly under root $v$ (`parent[find u] := find v`).
- Invariant & Post-condition: prove that after `find(v)`, all traversed nodes along the path have depth 1 (flattened star).
- Worst-case single operation: formalize the linear chain construction showing depth can reach $\Omega(n)$.
- Adversarial total work lower bound: formalize the adversarial construction demonstrating that $n$ operations can require $\Omega(n \log n)$ total steps.
- Amortized upper bound: prove that $m$ operations on $n$ elements require at most $O((n + m) \log n)$ steps.
- Implement in `Amort/Graph/PathCompressionOnly.lean` and document in `Amort/Graph/PathCompressionOnly.md`.

### R2. Algorithmic Quicksort & Mathematical Correctness
- Formalize 3-way partitioning (`partition3`) or standard partitioning for `List α` with `[LinearOrder α]`.
- Define `quicksort` with well-founded recursion or fuel on list length.
- Prove complete algorithmic correctness:
  - Multiset/Permutation equivalence: `quicksort xs ~ xs`.
  - Sortedness: `(quicksort xs).Sorted (· ≤ ·)`.
  - Equivalence to Mathlib's `List.mergeSort` and `List.insertionSort`.
- Implement in `Amort/Sorting/Quicksort.lean`.

### R3. Quicksort Worst-Case Complexity ($\Theta(n^2)$)
- Formalize comparison counting for naive pivot selection (e.g. head element on sorted or reverse-sorted input).
- Establish the recurrence $T(n) = T(n - 1) + (n - 1)$ for $n \ge 1$.
- Prove exact solution: $T(n) = \frac{n(n - 1)}{2}$.
- Connect with Mathlib `IsBigO`: worst-case comparison complexity is $\Theta(n^2)$ ($O(n^2)$ upper bound and $\Omega(n^2)$ lower bound under `Filter.atTop`).

### R4. Quicksort with Deterministic $O(n)$ Median (BFPRT Selection)
- Formalize the Blum-Floyd-Pratt-Rivest-Tarjan (BFPRT) "Median-of-Medians" selection invariant: selecting the median of block medians guarantees a balanced partition where both sublists have size $\le \lfloor \frac{7n}{10} \rfloor + 3$ for $n \ge 5$.
- Formalize the divide-and-conquer recurrence with deterministic median selection:
  $$T(n) \le T(\lfloor 7n/10 \rfloor) + T(\lfloor 3n/10 \rfloor) + c \cdot n$$
- Prove by induction / recurrence mapping to `Amort.Recurrence.MasterTheorem` that $T(n) \le C \cdot n \cdot \text{Nat.size } n$.
- Deduce that deterministic median-of-medians Quicksort has a **strictly worst-case $O(n \log n)$ runtime**.

### R5. Quicksort Average-Case Complexity ($O(n \log n)$)
- Formalize the average-case recurrence assuming uniform random pivot selection:
  $$\mathbb{E}[T(n)] = \frac{2}{n} \sum_{i=0}^{n-1} \mathbb{E}[T(i)] + (n - 1)$$
- Bridge this recurrence to the pairwise indicator backward analysis in `Amort.Randomized.Quicksort` establishing $\mathbb{E}[T(n)] \le 2n H(n) \le 2n \cdot \text{Nat.size } n$.
- Connect to Mathlib `IsBigO`: average-case expected comparisons are $O(n \log n)$ under `Filter.atTop`.

### R6. Integration & Textbook Documentation
- Expose all modules in `Amort.lean`.
- Document mathematical architecture, comparative analysis, and recurrence proofs in:
  - `Amort/Graph/PathCompressionOnly.md`
  - `Amort/Sorting/Quicksort.md`
  - Master documents `Amort/Sorting/Sorting.md` and `README.md`.

## Acceptance Criteria

### Correctness and Build
- [ ] The entire project builds cleanly with `lake build Amort` with 0 errors and 0 warnings.
- [ ] Zero `sorry` or `sorryAx` axioms used in any proof (verified with `#print axioms` / audit script).
- [ ] All code conforms to the Mathlib line-length limit ($\le 100$ characters).
- [ ] `quicksort_perm` and `quicksort_sorted` are proven without caveats.
- [ ] Worst-case $O(n^2)$ recurrence and exact closed form $\frac{n(n-1)}{2}$ are proven.
- [ ] Deterministic median-of-medians $O(n \log n)$ worst-case bound is proven.
- [ ] Average-case expected $O(n \log n)$ bound is proven.
- [ ] Iterative path-compression-only DSU operations and $O(m \log n)$ / $\Omega(n \log n)$ bounds are proven.
- [ ] All new modules are exported in `Amort.lean` and thoroughly documented.

## 2026-09-20T00:55:13Z

Formalize the foundational Distributed Systems Canon in Lean 4 within `Amort.Distributed`: Causality & Clocks, CAP & Two Generals Impossibility, Paxos & Raft Consensus, Byzantine Fault Tolerance ($3f+1$), and Chandy-Lamport Distributed Snapshots.

Working directory: /workspace/amort
Integrity mode: development

## Requirements

### R1. Causality & Logical Clocks (`Amort.Distributed.Causality`)
- Formalize distributed events and Lamport's happens-before relation ($\to$) as an irreflexive, transitive strict partial order.
- Formalize Lamport scalar clocks with tick and message-receive update rules, proving clock consistency: $e_1 \to e_2 \implies C(e_1) < C(e_2)$.
- Formalize Vector Clocks ($V : \text{Event} \to (\text{Fin } N \to \mathbb{N})$) with component-wise update rules, proving the strong causal isomorphism:
  $$V(e_1) < V(e_2) \iff e_1 \to e_2$$

### R2. Impossibility Theorems: CAP & Two Generals (`Amort.Distributed.Impossibility`)
- **Gilbert-Lynch CAP Theorem**:
  - Formalize an asynchronous network model with state transitions, read/write client events, linearizability (consistency C), and response guarantees (availability A).
  - Model network partitions: disconnected subsets $G_1, G_2$ where all inter-group messages are dropped.
  - Prove the Gilbert-Lynch impossibility: no distributed protocol can satisfy both linearizability and availability across a partition.
- **Two Generals' Problem**:
  - Formalize communication over an unreliable lossy channel where messages may be dropped.
  - Prove by induction on message delivery count that common knowledge of agreement can never be attained with certainty.

### R3. Crash-Tolerant Consensus: Paxos (Single-Decree & Multi-Paxos) and Raft (`Amort.Distributed.Consensus`)
- **Quorum Intersection Foundation**:
  - Prove the majority quorum intersection lemma: for any two quorums $Q_1, Q_2 \subseteq \text{Fin } N$ with $|Q_1|, |Q_2| > N / 2$, $Q_1 \cap Q_2 \ne \emptyset$.
- **Single-Decree Paxos (Synod Protocol)**:
  - Formalize ballot identifiers (`Ballot = ℕ × Fin N`) with total lexicographic ordering.
  - Formalize the two-phase protocol state machine:
    - Phase 1a (`Prepare(b)`) and Phase 1b (`Promise(b, maxAcceptedBallot, maxAcceptedValue)`).
    - Phase 2a (`Propose(b, v)`) where proposer chooses $v$ corresponding to the highest ballot among responses in the promise quorum (or client proposed value if none).
    - Phase 2b (`Accept(b, v)`): acceptors accept if no promise with $b' > b$ was made.
  - **Core Paxos Invariant**: If a value $v$ is chosen by an acceptance quorum at ballot $b$, then for any higher ballot $b' > b$, any proposal issued at $b'$ must have value $v$.
  - **Learner Agreement Theorem**: No two learners ever decide different values ($v_1 = v_2$).
- **Multi-Paxos Replicated Log**:
  - Formalize slot-indexed instances `Slot ℕ → SingleDecreePaxos`.
  - Prove state machine replication safety across committed log entries.
- **Raft Safety Invariants**:
  - Formalize Raft leader election, term monotonicity, and the Log Matching Invariant.

### R4. Byzantine Fault Tolerance ($3f + 1$) (`Amort.Distributed.BFT`)
- Formalize the Byzantine Generals problem where up to $f$ out of $N$ nodes can exhibit arbitrary (malicious) behavior.
- Prove the Lamport-Shostak-Pease Lower Bound: consensus in an unauthenticated system is impossible when $N \le 3f$ (formalize the 3-node, 1-traitor counterexample).
- Formalize the Oral Messages $OM(m)$ algorithm for $N \ge 3f + 1$, proving agreement and validity.
- Formalize PBFT Quorum Math: with $N = 3f + 1$, any two quorums of size $2f + 1$ intersect in at least $f + 1$ nodes, ensuring at least one non-faulty (honest) node in the intersection.

### R5. Consistent Global Snapshots (`Amort.Distributed.Snapshot`)
- Formalize the Chandy-Lamport distributed snapshot algorithm with marker-passing rules.
- Prove that the recorded global state forms a consistent cut: no message recorded in the channel state was sent after the snapshot was initiated.

### R6. Integration & Textbook Documentation
- Export all modules under `Amort.Distributed` in `Amort.lean`.
- Document mathematical architecture, message schemas, inductive invariants, and proof structures in `Amort/Distributed/Distributed.md` and dedicated chapter files.

## Acceptance Criteria

### Correctness and Build
- [ ] The entire project builds cleanly with `lake build Amort` with 0 errors and 0 warnings.
- [ ] Zero `sorry` or `sorryAx` axioms used in any proof (strictly standard Lean 4 foundational axioms).
- [ ] All code conforms to the Mathlib line-length limit ($\le 100$ characters).
- [ ] Vector clock causal isomorphism ($V(e_1) < V(e_2) \iff e_1 \to e_2$) is proven.
- [ ] Gilbert-Lynch CAP impossibility theorem is proven.
- [ ] Paxos majority quorum intersection and learner agreement safety are proven.
- [ ] Byzantine $N \le 3f$ impossibility and $N \ge 3f + 1$ quorum intersection are proven.
- [ ] Chandy-Lamport consistent cut property is proven.
- [ ] All modules are exported in `Amort.lean` and documented.

## 2026-09-23T04:09:22Z

Systematically resolve the proof gaps, vacuous definitions, and anti-patterns identified in `proof_review.md` across the Lean 4 formalization repository (`Amort/`), upgrading modules to satisfy the strict Definition of Done.

Working directory: `/workspace/amort`
Integrity mode: development

Reference: `proof_review.md` in repository root.

## Requirements

### R1. Phase 0 Guardrails & Anti-Pattern Elimination
Establish `Amort/Audit.lean` validating `#print axioms` on headline theorems, and eliminate recurring anti-patterns (A1–A10):
- Replace closed-form `…Work` formulas (A1) with real instrumented execution counters (`fooWithCount x : Output × ℕ` where `(fooWithCount x).1 = foo x`).
- Eliminate unconstructed hypotheses and assumed structure fields (A2).
- Ensure correctness and cost theorems operate on the real algorithm, not stand-in functions (A3).
- Remove tautological or near-tautological theorems (A4).
- Strengthen one-sided specifications to both soundness and optimality (A5).
- Ensure fuel usage includes an exhaustiveness theorem on valid inputs (A6).
- Ensure `IsBigO` left-hand sides represent actual instrumented execution runs rather than self-formulas (A7).

### R2. Phase 1 Pilot Nodes Upgrade
Bring all Phase 1 pilot nodes to solid (✅) status matching the Definition of Done:
- `GCD/EuclideanGCD.lean`: Implement `euclidGcd` and `euclidGcdWithSteps`, proving `euclidGcd = Nat.gcd` and step equality.
- `Sorting/InsertionSort.lean` & `Sorting/MergeSort.lean`: In-repo `sorted` and `perm` proofs; replace internal `splitInTwo` dependency with custom `split`.
- `DataStructure/DynamicArray.lean`: Provide an end-to-end bound from `initOne` with no assumed hypotheses.
- `DataStructure/TwoStackQueue.lean`: Prove FIFO correctness for `pop`.
- `String/KMP.lean`: Implement full `computePi` with fallback loop, prove `computePi_eq_piSpec`, implement pattern scanning loop, and link step counting and correctness to the same term.
- `Recurrence/BinarySearch.lean`: Implement executable binary search over sorted arrays, prove `found ↔ x ∈ a`, count probes, and connect to recurrence.

### R3. Phase 2 Missing Pieces
Resolve missing components in partially solid modules:
- `String/LCS.lean`: Add the optimality half (`∀ s, IsCommonSubsequence s xs ys → s.length ≤ lcsRec xs ys`), link bottom-up table to recursion, and count cell operations.
- `String/EditDistance.lean` & `DP/Knapsack.lean`: Formally prove bottom-up dynamic programming tables equal their recursive definitions and instrument table fill counts.
- `NumberTheory/ModExp.lean`: Link step counting directly to `modExpAux`.
- `Greedy/IntervalScheduling.lean`: Replace closed-form work with genuine scan steps plus sort cost.
- `Sorting/Quicksort.lean`: Link `quicksortWithCount` worst-case bound to actual comparison counts.
- `Graph/BellmanFord.lean`: Support `ℤ` weights and prove that `n - 1` passes yield shortest paths.
- `Graph/Traversal.lean`: Implement executable BFS with queue and visited state, proving distance optimality and `O(V + E)` step bounds.

### R4. Phases 3 & 4 Core & Advanced Rebuilds
Iterate through the core and advanced modules as scoped in `proof_review.md`:
- DSU: Implement union-by-rank, prove rank bounds, and define genuine unbounded $\alpha(n)$.
- Graph algorithms: Implement Dijkstra, Kruskal, Prim, and augmenting-path Max Flow.
- Data structures: Implement array-based Binary Heap with sift operations and Balanced BST insertions.
- String algorithms: Implement Z-box algorithm, Rabin-Karp matcher, and Trie/Aho-Corasick.
- Distributed & randomized protocols: Align definitions with honest step models, proving protocol invariants from step rules.
- Mark `Complexity/Classes.lean` as stub or out-of-scope while preserving genuine `KarpReductions.lean` and `TwoSAT.lean`.

### R5. Documentation & Truthfulness Alignment
Update `README.md` and all individual `.md` files across `Amort/` to strictly describe only theorems that are genuinely proved, clearly marking any unverified components as stubs.

## Acceptance Criteria

### Build & Axiom Integrity
- [ ] `lake build Amort && lake build` succeeds with 0 errors and 0 warnings.
- [ ] Zero `sorry`, `admit`, or `sorryAx` across all modified files.
- [ ] `#print axioms` on all headline theorems shows only `[propext, Classical.choice, Quot.sound]`.

### Anti-Pattern Elimination
- [ ] Automated check confirms no closed-form `def …Work (n : ℕ) : ℕ := <formula>` definitions exist in active headline results.
- [ ] All `IsBigO` complexity statements bound the execution of an instrumented function `(fooWithCount x).2`.

### Pilot & Phase Deliverables
- [ ] All 6 Phase 1 pilot nodes (`EuclideanGCD`, `InsertionSort`/`MergeSort`, `DynamicArray`, `TwoStackQueue`, `KMP`, `BinarySearch`) satisfy the 7-point Definition of Done in `proof_review.md`.
- [ ] `Amort/Audit.lean` builds cleanly and verifies all headline theorems.
- [ ] Documentation (`README.md` and module `.md` files) accurately reflects the verified status of every algorithm.

## 2026-09-23T14:26:16Z

<USER_REQUEST>
Comprehensively fix and verify the entire `Amort/` repository (all modules across Phases 0 to 4 in `proof_review.md`), eliminating all anti-patterns (A1–A10), implementing genuine executable algorithms with independent specifications and two-sided correctness, and proving actual execution step complexity, strictly validated by independent adversarial reviewers.

Working directory: `/workspace/amort`
Integrity mode: development

Reference: `proof_review.md` (all sections: §1 anti-patterns, §2 Definition of Done, §3 per-module review, §5 fix order, §7 Round 2 review, and §7.3 exact acceptance targets).

## Requirements

### R1. Complete Repository Scope & Anti-Pattern Elimination (Repo-Wide)
Resolve proof gaps and anti-patterns across all 97 modules in `Amort/`:
- Eliminate all closed-form `...Work` formulas (A1) repo-wide; every complexity result must bound instrumented executions `(fooWithCount x).2`.
- Eliminate unconstructed hypotheses and assumed structure fields (A2).
- Ensure all correctness and cost theorems operate on the real algorithm, with zero delegation to stand-in functions (A3).
- Remove tautological or near-tautological theorems (A4).
- Strengthen one-sided specifications to both soundness and optimality (A5).
- Ensure any fuel recursion has an exhaustiveness lemma on valid states (A6).
- Ensure all `IsBigO` statements bound instrumented runtimes rather than self-formulas (A7).
- Discard or truthfully label vacuous complexity classes (A9) while keeping genuine reductions.

### R2. Round 3 Immediate Acceptance Targets (§7.3)
Implement and verify the exact required theorems specified in §7.3:
1. **KMP (`String/KMP.lean`)**: Native linear fallback loop `computePi` / `computePiWithCount`, equivalence `computePi_getD = piSpec`, preprocessing bound $\le 2|P|$, native match loop `mem_kmpMatch_iff : s ∈ kmpMatch P T ↔ IsSubstringAt P T s`, and combined bound $\le 2(|T| + |P|)$.
2. **BFS (`Graph/Traversal.lean`)**: Independent `Reachable` and `IsWalkOfLength` definitions, two-sided distance correctness (`bfs_eq_top_iff` and `bfs_eq_coe_iff`), and in-loop step count $\le n + m$.
3. **Bellman-Ford (`Graph/BellmanFord.lean`)**: Path realization `bellmanFord_achieved`, optimality under independent `NoNegCycle` hypothesis `bellmanFord_optimal`, and negative cycle detection `hasNegCycleCheck_iff`.
4. **LCS & Knapsack Table Counts**: Inductive table row constructions with real cell fill counters (`lcsWithCount`, `knapsackWithCount`), retiring formula stand-ins `lcsTableCount` and `knapsackTableCount`.
5. **Binary Search & Interval Scheduling**: Index correctness `binarySearch_some_get : binarySearch xs x = some i → xs[i]? = some x`, and end-to-end `intervalSchedule_optimal` without caller-provided sort hypotheses.

### R3. Core & Advanced Module Rebuilds (Phases 3 & 4)
Systematically rebuild and verify the core and advanced algorithmic canons to meet the 7-point Definition of Done:
- **Graph & Optimization**: Dijkstra (executable priority queue/selection with two-sided distance correctness), Kruskal (spanning forest cut property), Prim, Augmenting-path Max-Flow (Ford-Fulkerson/Edmonds-Karp), DSU (union-by-rank with $2^{\text{rank}} \le \text{subtree\_size}$ and true unbounded $\alpha(n)$), and Bridges (Tarjan DFS).
- **Data Structures**: Array-based Binary Heap (siftUp/siftDown with build-heap bound), Balanced BST (AVL/Red-Black insertions and height bounds).
- **Strings**: Z-box algorithm, Rabin-Karp Las Vegas matcher, Trie/Aho-Corasick dictionary automata, Suffix Array + Kasai, and Suffix Tree online construction.
- **Randomized Algorithms & Approximation**: Quicksort expectation on Mathlib `PMF`, Universal Hashing, Karger Min-Cut, Metric TSP (MST + Euler tour + shortcutting), and Greedy Set Cover ($H_n$ bound).
- **Distributed Systems**: Prove protocol invariants (Paxos P2 proposal invariant, Raft log matching, Vector clock causal soundness, Chandy-Lamport execution) from actual protocol step transition rules.

### R4. Guardrails & Documentation Truthfulness
- Expand `Amort/Audit.lean` to validate `#print axioms` across every headline theorem in the repository.
- Update `README.md` and every `.md` file to truthfully describe verified theorems, with zero overclaiming.

## Acceptance Criteria

### Adversarial Verification Standard
- [ ] Every module is audited by an independent adversarial reviewer against the 7-point Definition of Done in §2 of `proof_review.md`.
- [ ] All exact theorem statements in §7.3 exist with their specified names and types.
- [ ] Self-certified completion without independent adversarial confirmation is disallowed.

### Build & Axiom Integrity
- [ ] `lake build Amort && lake build` succeeds across all compilation units with 0 errors and 0 warnings.
- [ ] Zero `sorry`, `admit`, or `sorryAx` anywhere in the repository.
- [ ] `#print axioms` on all headline theorems shows exclusively `[propext, Classical.choice, Quot.sound]`.

### Anti-Pattern Elimination
- [ ] Automated check confirms zero closed-form `def …Work (n : ℕ) : ℕ := <formula>` definitions in active results.
- [ ] All `IsBigO` complexity statements bound the execution of an instrumented function `(fooWithCount x).2`.
- [ ] All documentation reflects the exact scope of genuinely verified theorems.
</USER_REQUEST>
