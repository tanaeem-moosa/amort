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
