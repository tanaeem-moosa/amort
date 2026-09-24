# Proof Review — `Amort/` (all 97 Lean modules)

**Reviewed:** 2026-09-22 against commit `9a8ea47`
**Build status:** `lake build` succeeds (2141 jobs); 0 `sorry`, 0 `axiom`, 0 `native_decide`.
**Audience:** the agent fixing the proofs, and the author (who is the first learner of the tutorial).

> **Fixer: start at §9 (Round 4, 2026-09-25): Phases 0–2 are done; next is Phase 3, in the order listed there.** §8.2 shows the scripted-check style to copy; §7.3 lists the earlier theorem statements
> required next. Work is accepted only when those theorems exist with those statements (or strictly
> stronger ones) and are listed in `Amort/Audit.lean`. A self-reported "victory" is not evidence.
> §1–§6 still apply to all remaining modules.

A green build only means every proof type-checks. It does **not** mean the theorems say what
their names, docstrings and `.md` files claim. This review checks the *statements* against the
claims. Every module gets one of three grades:

| Grade | Meaning |
| :---: | :--- |
| ✅ **Solid** | Real algorithm, real spec, and the headline theorem is about that algorithm. Small polish at most. |
| 🟡 **Partial** | Some genuine content, but the headline claim (correctness or complexity) is missing, assumed, or disconnected from the algorithm. |
| 🔴 **Vacuous / misleading** | The headline theorem is a tautology, the key fact is assumed as a hypothesis or structure field, or the "algorithm" is a stand-in. |

`*/Asymptotics.lean` files only lift other modules' bounds to `IsBigO`, so each one gets the grade
of whatever it wraps (see §4).

---

## 1. Recurring anti-patterns (fix these everywhere)

These patterns account for almost every 🔴. For each one, the rule after the arrow is what the fixer should do.

### A1. Closed-form "work" functions
A cost is *defined* as the answer, then "proved" to be at most the answer.
```lean
def ukkonenWork (n : ℕ) : ℕ := 4 * n
theorem ukkonenWork_le_linear (n : ℕ) : ukkonenWork n ≤ 4 * n := le_rfl
```
Found in: `dijkstraWork`, `edmondsKarpWork`, `kosarajuWork`, `hierholzerWork`, `primWork`,
`kruskalTotalWork`, `dsuWork`, `dsuPCOWork`, `adversarialPCOWork`, `dsuAckermannWork`, `strassenWork`,
`standardMatrixMulWork`, `fftWork`, `fftPolyMulWork`, `naivePolyMulWork`, `sieveWork`,
`convexHullWork`, `closestPairWork`, `metricTSPWork`, `setCoverWork`, `vertexCoverWork`,
`twoSATWork`, `huffmanConstructionWork`, `intervalSchedulingWork`, `quicksortWorkBound`,
`quicksortAvgWorkBound`, `bfprtQuicksortBound`, `kargerSingleRunWork`, `kargerTotalWork`,
`hashLookupExpectedWork`, `heapsortExtractionWork`, `siftUpSteps`, `siftDownSteps`,
`onlineMedianInsertWork`, `medianQuerySteps`, `insertWork` (BBST and Trie), `rotationSteps`,
`tarjanBridgeWork`, `hopcroftKarpWork`, `simplexPivotWork`, `lpFeasibilityWork`, `kasaiWork`,
`zAlgorithmWork`, `rabinKarpWork`, `rabinKarpAverageWork`, `acTotalSearchWork`, `ukkonenWork`,
`lcsTableCount`, `editDistTableCount`, `bellmanFordStepCount`.

→ **Rule:** follow the pattern the GCD and insertion-sort modules already use. Write
`fooWithCount : Input → Output × ℕ` that **runs the algorithm** and ticks a counter at each
elementary operation. Prove `(fooWithCount x).1 = foo x`, then prove the bound on
`(fooWithCount x).2`. Delete every closed-form `…Work` definition, or rename it to `…Bound` and
use it only as the right-hand side of a bound theorem.

### A2. The key fact is assumed (hypothesis or structure field)
The hard lemma appears as an input instead of being proved:
- `ValidDSU.depth_le_rank` (DSU: the entire union-by-rank argument)
- `DijkstraSpec`, `BFSDistance` (and these are too weak anyway; see A5)
- `TightResidualCut` (max-flow/min-cut: assumes the saturated cut exists)
- `halls_marriage_theorem (h_sufficient : …)` (assumes the hard direction)
- `HarmonicCharging` (Set Cover: its fields *are* the proof)
- `ShortcutDecomposition`, `h_mst_le_opt`, `h_walk_eq_2mst` (Metric TSP)
- `UniversalHashFamily.collision_bound` (then "proves" the same bound)
- `VectorClockSystem.causal_sound` (assumes the characterisation it then derives)
- `SatisfiesPaxosProposalInvariant` (assumes Paxos's P2 invariant, the whole difficulty)
- `total_dsu_work_bound (h_step : …)` (assumes Tarjan's per-operation amortised bound)
- `DFSTreeState` fields, `CompactSuffixTree.internal_le`, `SuffixLinkTree` link-depth field,
  `Trie.depth_step`, `AhoCorasick.fail_depth_lt`, `PrimFrontier.key_spec`, `ChandyLamportExecution.fifo_after`

→ **Rule:** a structure may bundle *data plus the invariant the algorithm maintains* only if some
definition in the file **constructs** a value of that structure from the algorithm's run, e.g.
`def runDijkstra … : DijkstraResult w s`. If nothing constructs it, the theorem is conditional, and
its name and docs must say "assuming X". Modelling assumptions (FIFO channels, a synchrony model)
may stay as hypotheses, but they must be listed in the module doc under **Assumptions**.

### A3. Stand-in algorithm
- `kmpMatch P T := naiveMatch P T` (KMP's correctness theorem is about the naive matcher)
- `kahnWork adj L := bfsWork adj L`, and `bfsWork` is a sum over an *arbitrary* list `L`, not a BFS
- `quicksortAvgWorkBound := Randomized.quicksortWorkBound` (a formula)

→ **Rule:** the object in the correctness theorem, the object in the cost theorem and the object
the docs call "the algorithm" must be the same Lean term.

### A4. Tautological or near-tautological theorems
`n ≤ 4 * n`, `n - 1 ≤ n`, `2 * n ≤ 4 * n` (Ukkonen); `mCard + 1 = mCard + 1` and
`√n + √n ≤ 2√n` (Hopcroft–Karp); `n / p ≤ n / p` (Sieve); `x ≤ x` (`suffixLink_chain_bound`);
`hullScan_operations_le` (LHS and RHS are the same term); `h : a = b → f a = f b`
(`rsm_safety`, `om_agreement_of_identical_votes`, `polyHash_congruence_soundness`,
`polyHash_mod_congruence`); `a < a + positive` (`obj_increases_of_pivot`);
`channel_state_soundness` (a projection of its own hypothesis); every `fooWork_le` from A1.

→ **Rule:** delete them. If a statement is needed as a rewrite, make it a `@[simp] lemma` with an
honest name, and never cite it as a result in the `.md` docs.

### A5. Specs too weak (only one direction)
- `DijkstraSpec` and `BFSDistance` only require `dist v ≤ dist u + w u v` and `dist s = 0`. The
  function `dist ≡ 0` satisfies both, so "`dist ≤` every path weight" says nothing about shortest
  paths. A shortest-path spec needs **both** `dist v ≤ weight p` for every path `p` from `s` to `v`
  **and** "some path achieves `dist v`" (or `dist v = ⊤` iff `v` is unreachable).
- `lcs_is_maximal` only proves that *some* common subsequence has length `lcsRec`. The optimality
  half ("every common subsequence has length ≤ `lcsRec`") is missing.
- `TopologicalSort`: only "a topological order implies acyclic". The converse (a DAG has one) is missing.

→ **Rule:** every optimisation result needs **soundness** (achievable) **and** **optimality**
(nothing better exists), stated against a spec that is independent of the algorithm. The
`Knapsack`, `LIS` and `EditDistance` modules show the right shape.

### A6. Fuel that makes the bound trivial
`DSU.findSteps` recurses with fuel `Nat.size n`, so `findSteps ≤ Nat.size n` holds by
truncation, not by union-by-rank. (`PathCompressionOnly` uses fuel `n`, which is fine as a
termination device, but it still needs a lemma that the fuel is never exhausted on valid states.)

→ **Rule:** fuel is only acceptable with a theorem that the fuel-bounded result equals the
unbounded one on valid inputs, as `Sorting/Quicksort.lean` does with `quicksortFuel_eq_of_ge`.

### A7. `IsBigO` of a formula against itself
Examples: `isBigO_bfsWork_atTop : (n+m) =O (n+m)`, `isBigO_kahnWork_atTop`,
`isBigO_trieBuildWork_atTop : p =O p`, `isBigO_dynArrayTotalCost_atTop : 3k =O k`,
`isBigO_naiveMatch_bound_atTop`.
→ **Rule:** the left side of every `IsBigO` must be the cost of a real run
(`fun x ↦ (fooWithCount x).2`), not a formula.

### A8. Misleading names
- `invAck` is a **hard-coded lookup table capped at 5** (`invAck n = 5` for all `n > 65533`). It is
  bounded by a constant, so every "Θ((m+n)·α(n))" result is literally Θ(m+n) and says nothing
  about the inverse Ackermann function. Define `α(n) := Nat.find (∃ k, n ≤ ack k 1)`, using
  Mathlib's `ack` and its unboundedness lemmas, and prove it is unbounded.
- `max_flow_min_cut` only proves "a saturated cut with no backflow has capacity equal to the flow
  value". The actual theorem (max flow = min cut, via an augmenting-path argument) is absent.
- `Recurrence/MasterTheorem.lean` covers exactly one case, `T(n) ≤ T(⌈n/2⌉) + T(⌊n/2⌋) + cn`.
  Rename it (e.g. `DivideAndConquer2`) or generalise it to `a·T(n/b) + f(n)`.
- `Distributed/Impossibility.lean` contains no FLP. It has a toy CAP model and a toy Two Generals model.
- `lsp_three_node_impossibility` is a one-round, three-message toy, not the general `n ≤ 3f` bound.

### A9. The model itself is vacuous
`Complexity/Classes.lean`: `Decider` bundles an **arbitrary** function `List α → Bool` with two
numbers `polyCoeff`/`polyExp` that nothing ties to the function. Classically, *every* language is
`InP` (take `decide x := decide (x ∈ L)`), so `InP`, `InNP`, `IsNPHard` and
`inP_of_polyReducible` carry no complexity content. The same applies to `PolyReduction.toFun`,
which is unconstrained apart from an output-length bound.
→ **Rule:** either base the classes on Mathlib's machine model
(`Turing.TM2ComputableInPolyTime` in `Mathlib/Computability/TMComputable.lean`), or delete the P/NP
layer and keep only the combinatorial equivalences (`KarpReductions.lean`), which are genuine.

### A10. Docs overclaim
The `.md` files and the `README.md` present most of the above as "formalized" or "verified". For
example, `TwoStackQueue.lean`'s module doc lists a `pop_spec` theorem that does not exist.
→ **Rule:** every fix PR must update the matching `.md`. A doc may only name a theorem that exists.
Anything conditional must be labelled *"conditional on …"*.

---

## 2. Definition of Done for a "solid" node

Use this checklist per module. A node enters the tutorial only when every box is ticked.

1. **Algorithm:** an executable `def` of the algorithm itself, not a spec or a formula.
   Termination is by structural or `termination_by` recursion, or by fuel with an
   exhaustiveness lemma (A6).
2. **Spec:** an independent mathematical specification, not defined in terms of the algorithm.
3. **Correctness:** `algo x` meets the spec, in both directions for search and optimisation
   problems (A5).
4. **Cost:** `algoWithCount` with `(algoWithCount x).1 = algo x`, and an explicit bound on
   `(algoWithCount x).2` whose only hypotheses are input preconditions.
5. **Asymptotics (optional):** an `IsBigO` whose left side is `(algoWithCount x).2`.
6. **Hygiene:** `#print axioms` on the headline theorems shows only `propext`, `Classical.choice`
   and `Quot.sound`. No theorem is provable by `le_rfl`/`rfl`/`omega` from definitions alone
   (unless it is a named simp lemma). No closed-form `…Work` definitions.
7. **Docs:** the `.md` lists exactly the theorems that exist, with their honest scope.

Suggested guardrail: add `Amort/Audit.lean`, which runs `#print axioms` on every headline theorem,
plus a CI grep that fails on `def \w*(Work|Steps|Cost)\w* \(n : ℕ\).*: ℕ :=` followed by an
arithmetic expression. Existing exceptions are then renamed to `…Bound`.

---

## 3. Per-module review

### 3.1 GCD — ✅ best module in the repo (pilot-ready)

| File | Grade | Genuinely proved | Issues / fix |
| :--- | :---: | :--- | :--- |
| `GCD/BinaryGCD.lean` | ✅ | `binaryGcd_eq_gcd` for all `a b`; clean parity lemmas | None. |
| `GCD/StepCount.lean` | ✅ | `binaryGcdWithSteps` linked to `binaryGcd` and `binaryGcdSteps`; `≤ size a + size b` | This is the model pattern for A1. |
| `GCD/EuclideanGCD.lean` | 🟡 | `euclideanGcdSteps ≤ 2·size(min a b)+1`; modulo-halving lemmas | There is no Euclid *algorithm* in the repo: the steps function "mirrors" Mathlib's `Nat.gcd`. Add `euclidGcd` + `euclidGcdWithSteps`, prove `euclidGcd = Nat.gcd` and `.2 = euclideanGcdSteps`. **Good first exercise for the author.** |
| `GCD/Asymptotics.lean` | ✅ | Real `IsBigO` of real step counts | Fine. |

### 3.2 Sorting — mostly ✅ (pilot-ready)

| File | Grade | Genuinely proved | Issues / fix |
| :--- | :---: | :--- | :--- |
| `Sorting/InsertionSort.lean` | ✅ | Comparison count linked to Mathlib's `List.insertionSort`; `≤ n(n-1)/2` | Correctness is inherited from Mathlib. For the tutorial, add in-repo `sorted`/`perm` proofs (the Prove step). |
| `Sorting/MergeSort.lean` | ✅ | Count linked to Mathlib's `mergeSort`; `≤ n·size n` | Depends on `List.MergeSort.Internal.splitInTwo`, which is **internal API** and will break on toolchain bumps. Define your own `split`. |
| `Sorting/DecisionTree.lean` | ✅ | `leafCount ≤ 2^depth`; evaluation lands in the leaves | Fine. |
| `Sorting/LowerBound.lean` | ✅ | `n! ≤ 2^depth` for any tree that distinguishes permutations; `log n! = Θ(n log n)` | Excellent. Optional: exhibit merge sort as a decision tree so the bound applies to a concrete algorithm. |
| `Sorting/Quicksort.lean` | 🟡 | Deterministic quicksort: `perm`, `sorted`, fuel-exhaustiveness lemma ✅ | `quicksortWorstCaseRec` is a recurrence not linked to any comparison count. `bfprtQuicksortRec` is defined but never bounded; `bfprtQuicksortBound` is a formula (A1). `IsQuicksortAvgRec`/`quicksortAvgRec` are defined but never solved. `quicksortAvgWorkBound` is a formula. Fix: add `quicksortWithCount`, prove the worst case `≤ n(n-1)/2` and that it is attained on sorted input. Remove the BFPRT/average sections or finish them. |
| `Sorting/Asymptotics.lean` | ✅ / 🟡 | Insertion and merge sort parts are real | The quicksort parts inherit the 🟡. |

### 3.3 Recurrence toolkit — ✅ (library lemmas, not algorithms)

| File | Grade | Notes |
| :--- | :---: | :--- |
| `Recurrence/Telescoping.lean` | ✅ | Genuine telescoping bounds. |
| `Recurrence/Halving.lean` | ✅ | `T(n) ≤ T(n/2)+c ⇒ O(log n)`; `size = O(log)`. Genuine. |
| `Recurrence/MasterTheorem.lean` | ✅ (misnamed) | Only the `2T(n/2)+cn` case (A8). Rename or generalise. |
| `Recurrence/Composition.lean` | ✅ | Generic `IsBigO` sum/product lemmas. Fine. |
| `Recurrence/DP.lean` | 🟡 | `DPModel` is "∑ over states of *arbitrary* per-state costs ≤ #states × bound". It is true, but it is not tied to any computation, and every DP module uses it as if it were the DP's running time. Fix: keep it as a lemma, but DP costs must come from an instrumented table fill (A1). |
| `Recurrence/BinarySearch.lean` | 🔴 | There is **no binary search**, only a recurrence `binarySearchSteps`. Fix: implement binary search over a sorted `Array`, prove `found ↔ x ∈ a` and count the probes. The recurrence lemma then becomes the Analyze step. (This is a pilot-tier node in the plan.) |

### 3.4 Data structures

| File | Grade | Genuinely proved | Issues / fix |
| :--- | :---: | :--- | :--- |
| `DataStructure/DynamicArray.lean` | 🟡→✅ | Potential Φ = 2·size − cap; amortised push = 3; telescoping ✅ | Missing an **end-to-end theorem without hypotheses**, e.g. `pushSeqCost k initOne ≤ 3k + 1`. The `hle`/`hphi` side conditions can be discharged with `pushSeq_size_le_capacity` and a lemma `cap ≤ 2·size` after the first push. It only models (size, capacity). Optional: model the element buffer and prove `get` after `push`. **Pilot node: do this first.** |
| `DataStructure/TwoStackQueue.lean` | 🟡→✅ | Amortised ≤ 3 per operation; total ≤ 3·ops from empty ✅ | **No functional correctness for `pop`** (the doc claims a `pop_spec` that does not exist). Add `pop q = (q.toList.head?, q')` with `q'.toList = q.toList.tail`. |
| `DataStructure/BinaryHeap.lean` | 🟡 | `buildHeapWork n k := ∑ (n/2^h)·h ≤ 2n` is a genuine and nice sum bound | No heap operations exist (`siftUp`, `siftDown`, `insert`, `extractMin`), and no heapsort. `siftUpSteps d := d` and `siftDownSteps h := 2h` are formulas. Fix: implement an array-based heap and prove the heap invariant is preserved, then link build-heap's actual sift count to `buildHeapWork`. |
| `DataStructure/BalancedBST.lean` | 🔴 | Rotations preserve `toList`/`size` ✅; `rankSteps ≤ height` ✅ | No insert/delete/rebalance, and balance is *assumed* (`IsHeightBalanced c`). `rank`/`select`/`find` have no correctness theorems. Every `…Steps` walks both subtrees (`1 + max`), so it equals the height and ignores the key. Fix: implement AVL insert, prove BST, AVL and `toList` invariants and the height ≤ 1.44·log bound. That is a large job, so defer it after the pilot. |
| `DataStructure/OnlineMedian.lean` | 🟡 | "Max of low half is a median" under the balance and partition invariants ✅ | No insert/rebalance operation, the halves are lists rather than heaps, and the costs are constants (A1). Fix: implement `insert` and prove it preserves `Valid`. |
| `DataStructure/Asymptotics.lean` | 🔴 | Only `buildHeap` is real | The rest are A7 (e.g. `3k =O k`). |

### 3.5 Strings

| File | Grade | Genuinely proved | Issues / fix |
| :--- | :---: | :--- | :--- |
| `String/NaiveMatch.lean` | ✅ | `mem_naiveMatch_iff` (sound and complete); count ≤ `(n−m+1)·m` ✅ | Pilot-ready. |
| `String/KMP.lean` | 🔴 | `kmpStep`'s potential argument (`steps + j' ≤ j + 2`) is genuine and the right idea | `kmpMatch := naiveMatch` (A3). `piSpec` is a brute-force spec of π, and **no `computePi` exists**. Nothing records matches during the scan, so the step bound applies to a scan whose output is never checked. Fix (headline node, see the plan's quest card): (1) `computePi` using the same fallback loop; (2) `computePi_eq_piSpec`; (3) a scan that emits the positions `i` where `j` reaches `|P|`; (4) `kmpMatch_eq` / `mem_kmpMatch_iff` for *that* scan; (5) `kmpWithCount` linked to it; (6) the step bound on it. |
| `String/ZAlgorithm.lean` | 🟡 | `zSpec` and the pattern-matching reduction `P ++ [#] ++ T` ✅ | **No Z-algorithm**: `ZWindow` is unused and `zAlgorithmWork := 2n`. Fix: implement the Z-box loop, prove it equals `zSpec`, count the comparisons. |
| `String/RabinKarp.lean` | 🟡 | Rolling-hash algebra (sliding window, mod `p`) ✅ | No matcher. The "soundness" theorems are A4. Fix: implement the verify-on-hash-hit matcher (always correct, as a Las Vegas algorithm), prove `↔ IsSubstringAt`, and state the worst-case cost with an explicit collision count. |
| `String/Trie.lean` | 🟡 | `walk_depth`, `contains_soundness` (on an abstract `Trie` whose invariants are fields, A2) | `PrefixTrie.insert`/`lookup` are real but have **no correctness theorem**. Fix: `lookup (build ps) w = true ↔ w ∈ ps`. Remove or construct the abstract `Trie` record. |
| `String/AhoCorasick.lean` | 🟡 | `acStep`/`acScan` potential bound ≤ 2·\|T\| ✅ (the KMP argument generalised) | Failure links are arbitrary fields (no construction). There is no match output and no correctness. `acTotalSearchWork` is a formula. Large job; defer after KMP. |
| `String/LCS.lean` | 🟡 | `lcsWitness` is a common subsequence of length `lcsRec` ✅ | **Optimality half missing** (A5): add `∀ s, IsCommonSubsequence s xs ys → s.length ≤ lcsRec xs ys`. `lcsTable` is never proven to agree with `lcsRec`. `lcsTableCount` is a formula. |
| `String/EditDistance.lean` | ✅ / 🟡 | `editDist_is_minimal_alignment` (both directions) ✅ excellent | The `editDistTable` row DP is never proven equal to `editDistRec` (only its length); `editDistTableCount` is a formula. Add the table-correctness theorem. |
| `String/SuffixArray.lean` | 🔴 | `lcp` bounds (trivial) | No construction and no Kasai. `KasaiHeightInvariant` is hypothetical; `kasaiWork := 2n`. |
| `String/SuffixTree/CompactTree.lean` | 🔴 | — | The node-count bounds are structure fields (A2). |
| `String/SuffixTree/SuffixLink.lean` | 🔴 | `iterateLink_depth` (from an assumed field) | `suffixLink_chain_bound : x ≤ x` (A4). |
| `String/SuffixTree/Ukkonen.lean` | 🔴 | — | Entirely A1 and A4. Rebuild from scratch in the last phase: a faithful Ukkonen verification is the largest job in the repo. Start with a naive suffix trie, then the compact tree, then suffix links, then the online construction. |
| `String/Asymptotics.lean`, `AdvancedAsymptotics.lean`, `SuffixTree/Asymptotics.lean` | 🔴 / 🟡 | The naive-match parts are real | KMP, Z, Rabin–Karp, Kasai, Trie, AC and Ukkonen are A7. |

### 3.6 Dynamic programming

| File | Grade | Genuinely proved | Issues / fix |
| :--- | :---: | :--- | :--- |
| `DP/Knapsack.lean` | ✅ / 🟡 | `knapsack_is_optimal`: sound and complete against subsets ✅ | `knapsackRec` is the exponential top-down recursion. There is no table, and the `knapsackGridDP` cost is `unitGridDP`, which is unrelated to the recursion. Add a bottom-up table, prove it equals `knapsackRec`, and count the cell fills. |
| `DP/LIS.lean` | ✅ / 🟡 | `lis_is_optimal` (both directions) ✅ | The cost model `lisDP` (cost per state = `i`) is invented. The plan's LIS node depends on binary search (patience sorting, O(n log n)), which does not exist. |
| `DP/MatrixChain.lean` | 🔴 | Only `matrixChainCost_self` and state counting | **No correctness**: there is no definition of parenthesisation trees and no proof that `matrixChainCost` is their minimum. The cost model is invented. |
| `DP/Asymptotics.lean` | 🔴 | — | Wraps the invented `DPModel` costs (A7). |

### 3.7 Graphs

| File | Grade | Genuinely proved | Issues / fix |
| :--- | :---: | :--- | :--- |
| `Graph/Traversal.lean` | 🔴 | Handshake lemma, `edgeList_length` ✅ | **No BFS/DFS algorithm.** `bfsWork` sums over an arbitrary list. `BFSDistance` is satisfied by `dist ≡ 0` (A5). Fix: implement BFS with a queue and a visited set, prove `dist v = min path length` (both directions) and `steps ≤ n + m`. |
| `Graph/TopologicalSort.lean` | 🟡 | A topological order implies no cycles ✅ | No Kahn/DFS algorithm; `kahnWork = bfsWork` (A3); the converse is missing. |
| `Graph/SCC.lean` | 🟡 | Mutual reachability is an equivalence; SCCs are disjoint; the condensation has no 2-cycles ✅ | No Kosaraju/Tarjan; `kosarajuWork` is a formula. |
| `Graph/Dijkstra.lean` | 🔴 | `pathWeight` lemmas | `DijkstraSpec` is satisfied by zero (A5); `greedy_choice_minimal` is a restatement of its hypothesis; there is no algorithm; the work is a formula. |
| `Graph/BellmanFord.lean` | 🟡 | The algorithm is real; the pass count is linked (`= (n−1)·m`) ✅; monotonicity ✅ | **No correctness theorem** (that after `n−1` passes, `dist` equals the shortest path). Weights are `ℕ`, which removes the reason Bellman–Ford exists (negative edges and negative-cycle detection). Fix: use `ℤ` weights and prove "k passes give the shortest paths using ≤ k edges". |
| `Graph/FloydWarshall.lean` | 🟡 | The recursion is real; monotonicity ✅ | **No correctness** (`fw k i j` = the shortest path with intermediate vertices `< k`). The `FWState` cost is unrelated to the recursion, which is exponential as written. |
| `Graph/Kruskal.lean` | 🔴 | The sort bound is real (reuses `mergeSortCount`) | No Kruskal, no spanning tree, no cut property; `head_min_cut_edge_of_sorted` is trivial. The work is a formula. |
| `Graph/Prim.lean` | 🔴 | — | No algorithm. `PrimFrontier.key_spec` compares keys with **vertex indices** (`(witness v).val + u.val`), which is almost certainly a bug. The work is a formula. |
| `Graph/MaxFlow.lean` | 🟡 | `flow_cut_identity`, `weak_duality` ✅ (nice) | `max_flow_min_cut` is misnamed (A8): it assumes the tight cut. No augmenting paths, Ford–Fulkerson or Edmonds–Karp. Fix: residual graph + "no augmenting path ⇒ reachable set is a tight cut". Edmonds–Karp's O(VE²) is large; defer it. |
| `Graph/DSU.lean` | 🔴 | — | No `union`/`find` operations. `ValidDSU.depth_le_rank` is assumed (A2), `treeSize` is unconnected to `parent`, and the fuel is `size n` (A6). Fix: implement union-by-rank + find, prove `2^rank ≤ subtree size` is preserved, and derive `depth ≤ log n`. |
| `Graph/PathCompressionOnly.lean` | 🟡 | Real `findRoot`/`compressPath`/`unite`; compression sets depth to 1 ✅; the linear chain has depth `n−1` ✅ | The chain is built by hand, not by a sequence of `unite` calls. `adversarialPCOWork` and `dsuPCOWork` are formulas (A1), so the "Ω(n log n)" and "O(m log n)" claims are unproven. |
| `Graph/Eulerian.lean` | 🔴 | Σ indegree = Σ outdegree ✅ (trivial) | No Euler theorem and no Hierholzer; the work is a formula. |
| `Graph/Ackermann/AckermannHierarchy.lean` | 🟡 | `ack` values and monotonicity ✅ | Duplicates Mathlib's `ack`. **`invAck` is a capped lookup table (A8)**, so all of its consumers are meaningless. |
| `Graph/Ackermann/PathCompression.lean` | 🔴 | `compress` preserves the strict rank hierarchy (single pointer) ✅ | `SubtreeRankBound` is assumed, and its preservation is trivial because ranks never change. |
| `Graph/Ackermann/PotentialBound.lean` | 🔴 | `amortized_telescoping_sum` ✅ (generic) | `dsuAckermannWork` is a formula; `total_dsu_work_bound` assumes the per-operation bound (A2). The "strict two-sided Theta bound" in commit `4e2f5d8` is algebra on its own definition. |
| `Graph/Ackermann/Asymptotics.lean` | 🔴 | — | The Θ results are about a formula, and with the capped `invAck` they reduce to Θ(m+n). |
| `Graph/Advanced/BridgeTarjan.lean` | 🔴 | — | No graph appears in the definitions: `IsBridge` is *defined* as `disc u < low v`, so `bridge_characterization` just unfolds that definition. |
| `Graph/Advanced/HallMarriage.lean` | 🔴 | Necessity ✅ | Sufficiency is assumed. Use Mathlib's `Finset.all_card_le_biUnion_card_iff_exists_injective`, or prove it via max-flow once that is real. |
| `Graph/Advanced/HopcroftKarp.lean` | 🔴 | — | Entirely A4/A1. |
| `Graph/Asymptotics.lean`, `AdvancedAsymptotics.lean`, `Advanced/Asymptotics.lean` | 🔴 | The Bellman–Ford pass count is real | Everything else is A7. |

### 3.8 Greedy

| File | Grade | Genuinely proved | Issues / fix |
| :--- | :---: | :--- | :--- |
| `Greedy/IntervalScheduling.lean` | ✅ | The greedy output is pairwise compatible; the **exchange-argument optimality** holds for input sorted by finish time ✅ | Remove `intervalSchedulingWork` (A1). The scan cost is `greedyScanSteps = n`, so add the sort cost by reusing merge sort's count. Strong tutorial node. |
| `Greedy/Huffman.lean` | 🔴 | `costAtDepth` identity ✅ | No Huffman algorithm and no optimality. `huffman_greedy_choice_property` is an inequality about eight natural numbers, not about trees. |
| `Greedy/MedianOfMedians.lean` | 🟡 | The BFPRT recurrence `T(n) ≤ T(n/5)+T(7n/10+6)+cn ⇒ O(n)` ✅ (genuine) | No select algorithm; "pivot quality" is arithmetic on counts, not on elements. |
| `Greedy/Asymptotics.lean` | 🟡 | The BFPRT part is real | The rest is A7. |

### 3.9 Number theory and algebra

| File | Grade | Genuinely proved | Issues / fix |
| :--- | :---: | :--- | :--- |
| `NumberTheory/ExtendedGCD.lean` | ✅ | Bézout, `= Nat.gcd`, step count linked to Euclid ✅ | Pilot-ready. |
| `NumberTheory/ModExp.lean` | ✅ / 🟡 | `modExp_correct` ✅ | `modExpMulSteps` is a separate function, not proven to count `modExpAux`'s multiplications. Add `modExpWithCount`. |
| `NumberTheory/Sieve.lean` | 🔴 | A characterisation of primes (not a sieve) | No sieve algorithm. `markings_per_prime_le : n/p ≤ n/p`. `sieveWork` is a formula (and n log n is not the n log log n bound). |
| `Algebraic/FFT.lean` | 🟡 | Cooley–Tukey decomposition, butterfly identities, dyadic recurrence ✅ | **No FFT algorithm**, and no `fft ω a = dft n ω a`. `fftWork` and `fftPolyMulWork` are formulas. Fix: a recursive FFT on lists of length `2^k`, proven equal to `dft`, with an operation count. |
| `Algebraic/Strassen.lean` | 🟡 | The 2×2 identity ✅ and the `7T(n/2)+cn²` recurrence ✅; `log₂7 < 3` ✅ | No recursive block algorithm on `2^k × 2^k` matrices, so the recurrence is not linked to anything. `strassenWork := 7^size n` (A1). |
| `NumberTheory/Asymptotics.lean`, `Algebraic/Asymptotics.lean` | 🟡 / 🔴 | The ModExp and ExtGCD parts are real | The Sieve, FFT and Strassen parts are A7. |

### 3.10 Complexity, approximation, LP

| File | Grade | Genuinely proved | Issues / fix |
| :--- | :---: | :--- | :--- |
| `Complexity/Classes.lean` | 🔴 | Closure of polynomial bounds ✅ (arithmetic) | **The model is vacuous** (A9). **Out of scope:** delete it or mark it as a stub, rather than rebuilding it. |
| `Complexity/KarpReductions.lean` | ✅ | **3SAT ↔ independent set of size m** (both directions, 100+ lines) ✅; IS/VC/Clique complement dualities ✅ | Defines its own `SimpleGraph`, shadowing Mathlib's; switch to Mathlib's. The polynomial size of the reduction is only stated as edge-count formulas. |
| `Complexity/TwoSAT.lean` | ✅ / 🟡 | **2-SAT satisfiable ↔ no `x ⇝ ¬x ⇝ x`** (both directions) ✅ | No algorithm (`reachFinset` is noncomputable), and `twoSATWork` is a formula. The characterisation itself is a good node. |
| `Approximation/VertexCover.lean` | ✅ / 🟡 | Matching ≤ cover; a maximal matching yields a 2-approximation ✅ | No greedy maximal-matching algorithm; the work is a formula. |
| `Approximation/MetricTSP.lean` | 🔴 | `dist_le_walkCost` ✅ | All three hard facts are hypotheses (A2); the theorem is two lines of arithmetic. |
| `Approximation/SetCover.lean` | 🔴 | Harmonic-number lemmas ✅ | `HarmonicCharging` assumes the proof; no greedy algorithm. |
| `LP/Duality.lean` | ✅ | Weak duality, the optimality certificate, unbounded ⇒ dual infeasible ✅ | Fine as long as the docs do not claim strong duality. |
| `LP/Simplex.lean` | 🔴 | Ratio-test feasibility for one column ✅ (small) | No pivot that produces a new dictionary, no simplex loop, no termination. `obj_increases_of_pivot` is A4. |
| `Complexity/Asymptotics.lean`, `Approximation/Asymptotics.lean`, `LP/Asymptotics.lean` | 🔴 | — | A7. |

### 3.11 Randomized

| File | Grade | Genuinely proved | Issues / fix |
| :--- | :---: | :--- | :--- |
| `Randomized/Quicksort.lean` | 🔴 | `∑ (n−k)·2/(k+1) ≤ 2n·H_n` ✅ (arithmetic) | `expectedQuicksortComparisons` is **defined** as that sum. No random process and no link to quicksort. Fix: use Mathlib's `PMF` to define randomised quicksort and derive the expectation. This is hard, so defer it. |
| `Randomized/KargerMinCut.lean` | 🟡 | Telescoping product `∏ (n−2)/n = 2/(n(n−1))` ✅ | No graph contraction and no probability space; the work is a formula. |
| `Randomized/UniversalHash.lean` | 🔴 | Reservoir identity ✅ (arithmetic) | `collision_bound` is assumed and then restated. Fix: prove that `((a·x+b) mod p) mod m` is universal. |
| `Randomized/Asymptotics.lean` | 🔴 | — | A7. |

### 3.12 Distributed (honest toys at best)

| File | Grade | Genuinely proved | Issues / fix |
| :--- | :---: | :--- | :--- |
| `Distributed/Consensus.lean` | 🟡 | Majority quorums intersect ✅; Raft election safety within one term ✅ (small) | Paxos agreement assumes P2 (A2); `rsm_safety` is A4; Raft log matching is defined but never proved. |
| `Distributed/BFT.lean` | 🟡 | PBFT quorum intersection ≥ f+1 and it contains an honest node ✅; three-general one-round impossibility ✅ (toy) | `om_validity` is arithmetic and `om_agreement_of_identical_votes` is A4; no OM(m). |
| `Distributed/Causality.lean` | 🟡 | Lamport clock consistency ✅ | The vector-clock results assume `causal_sound` (A2). Fix: define the vector-clock update rules on an execution and prove `causal_sound`. |
| `Distributed/Snapshot.lean` | 🟡 | Consistent cut from the FIFO rule and the snapshot-before-marker rule ✅ (small, honest *given* these assumptions) | The protocol is never run. `channel_state_soundness` is A4. |
| `Distributed/Impossibility.lean` | 🟡 | Toy CAP (two nodes, one read); toy Two Generals ✅ | `SatisfiesAvailability := True` (the model hard-codes availability). No FLP (A8). Keep only if relabelled "toy model". |

These modules are in scope and are rebuilt in Phase 4 (§5). Until then, fix their docs so they no longer read as "canon formalised". Keep the modelling assumptions (FIFO channels, synchrony) as explicit hypotheses, but prove the protocol invariants (Paxos P2, vector-clock `causal_sound`) from the protocol's own step rules.

---

## 4. Scoreboard

| Grade | Modules |
| :---: | :--- |
| ✅ | BinaryGCD, GCD/StepCount, GCD/Asymptotics, InsertionSort, MergeSort, DecisionTree, LowerBound, Telescoping, Halving, MasterTheorem (misnamed), Composition, NaiveMatch, EditDistance (recursion), Knapsack (recursion), LIS (recursion), IntervalScheduling, ExtendedGCD, ModExp, KarpReductions, TwoSAT (characterisation), VertexCover (ratio), LP/Duality |
| 🟡 | EuclideanGCD, Sorting/Quicksort, Recurrence/DP, DynamicArray, TwoStackQueue, BinaryHeap, OnlineMedian, ZAlgorithm, RabinKarp, Trie, AhoCorasick, LCS, TopologicalSort, SCC, BellmanFord, FloydWarshall, MaxFlow, PathCompressionOnly, AckermannHierarchy, MedianOfMedians, FFT, Strassen, KargerMinCut, all of Distributed/* |
| 🔴 | Recurrence/BinarySearch, BalancedBST, KMP, SuffixArray, SuffixTree/* (3), MatrixChain, Traversal, Dijkstra, Kruskal, Prim, DSU, Eulerian, Ackermann/PathCompression, Ackermann/PotentialBound, Ackermann/Asymptotics, BridgeTarjan, HallMarriage, HopcroftKarp, Huffman, Sieve, Complexity/Classes, MetricTSP, SetCover, Simplex, Randomized/Quicksort, UniversalHash, most `*/Asymptotics.lean` |

Roughly: about **a quarter of the modules are solid**, about a third are partial, and about 40% are vacuous or misleading.
All of the solid ones are introductory-to-intermediate. Everything marketed as "advanced"
(Ackermann DSU, Ukkonen, Edmonds–Karp, Hopcroft–Karp, FLP/CAP, Strassen/FFT complexity) is 🔴 or 🟡.

---

## 5. Fix order (aligned with the tutorial pilot)

**Phase 0: guardrails (do first, small).**
1. Add `Amort/Audit.lean` (`#print axioms` for each headline theorem) and the CI grep for A1.
2. Rewrite `README.md` and each `.md` to list only what exists (A10). Mark 🔴 modules
   **"Status: stub — not verified"** at the top of their `.md` rather than deleting code.

**Phase 1: pilot nodes (make them fully ✅ by the Definition of Done in §2).**
1. `GCD/EuclideanGCD`: own `euclidGcd` + `WithSteps` link.
2. `Sorting/InsertionSort`, `Sorting/MergeSort`: in-repo `sorted` + `perm` proofs; replace `splitInTwo`.
3. `DataStructure/DynamicArray`: end-to-end bound from `initOne` with no hypotheses.
4. `DataStructure/TwoStackQueue`: FIFO correctness of `pop`.
5. `String/KMP`: the full rewrite described in §3.5 (the plan's showcase card).
6. `Recurrence/BinarySearch`: a real binary search (the Linear Scan → Binary Search gateway).

**Phase 2: already-strong nodes that need one missing piece.**
`String/LCS` (optimality half) · `String/EditDistance` and `DP/Knapsack` (table = recursion) ·
`NumberTheory/ModExp` (count link) · `Greedy/IntervalScheduling` (drop the formula, add the sort cost) ·
`Sorting/Quicksort` (worst-case count) · `Graph/BellmanFord` (ℤ weights + correctness) ·
`Graph/Traversal` (real BFS).

**Phase 3: rebuild core algorithms from scratch.**
DSU (union-by-rank, then a genuine α(n)), Dijkstra, Kruskal/Prim, Max-flow (augmenting path),
Heap/Heapsort, BST, FFT/Strassen algorithms, MatrixChain correctness, Z-algorithm, Rabin–Karp,
Trie/Aho–Corasick correctness, Huffman, Sieve, Eulerian/Hierholzer, SCC/topological-sort algorithms.

**Phase 4: advanced rebuilds (largest jobs, all in scope).**
Tarjan's inverse-Ackermann DSU bound (a real potential argument over real `union`/`find`),
path-compression-only Θ(m log n), suffix array + Kasai, suffix tree + Ukkonen,
Edmonds–Karp O(VE²), Hopcroft–Karp O(E√V), Bridges/Articulation points (Tarjan DFS),
Hall's theorem (sufficiency), Simplex (pivoting + termination under Bland's rule),
Metric TSP (MST + Euler tour + shortcutting), greedy Set Cover (H_n bound),
randomized algorithms on Mathlib's `PMF` (quicksort expectation, Karger, universal hashing),
and all of Distributed (Paxos, Raft log matching, vector clocks, Chandy–Lamport, OM(m), FLP).

**Out of scope: P/NP classes.** Delete `Complexity/Classes.lean` and the parts of
`Complexity/Asymptotics.lean` that depend on it (or leave them marked "stub, not verified").
Keep `KarpReductions.lean` and `TwoSAT.lean`: their combinatorial equivalences are genuine and
need no machine model.

---

## 6. Notes for the author as first learner

- **Learn from the ✅ modules first.** `GCD/StepCount.lean`, `Sorting/LowerBound.lean`,
  `String/EditDistance.lean`, `Complexity/KarpReductions.lean` and
  `Greedy/IntervalScheduling.lean` show real technique: `WithCount` linking, witness construction,
  exchange arguments and a big case analysis. They are worth reading closely.
- **Treat the 🔴 modules as anti-examples.** Before trusting any theorem, ask: *"Could I prove this
  if the algorithm were deleted?"* If yes, it isn't about the algorithm. This one question catches
  A1, A2, A4 and A7.
- **Keep a few fixes for yourself** rather than handing all of them to the agent. They are small,
  high-value exercises:
  1. `euclidGcd = Nat.gcd` (induction with `Nat.gcd.induction`),
  2. the LCS optimality half (induction on `xs.length + ys.length`, mirroring `lcsRec`),
  3. TwoStackQueue `pop` correctness (case split and `List.reverse` lemmas),
  4. DynamicArray end-to-end bound (discharging side conditions).
- When the agent rewrites KMP, read the diff against §3.5's six-step list. It is the best single
  lesson in the repo on how a correctness proof and an amortised cost proof attach to the *same*
  function.

---

## 7. Round 2 review (2026-09-23): agy's first fix pass

**Scope checked:** the uncommitted working tree on `docs/proof-review` (37 files, +2521/−497).
**Build:** `lake build` succeeds (2142 jobs). `Amort/Audit.lean` shows only
`propext`/`Classical.choice`/`Quot.sound`, with no `sorryAx`.

**Agy's self-audit was wrong.** Its handoff claims "VICTORY CONFIRMED" and says A1–A10 were
"eliminated repo-wide". In fact 52 closed-form cost definitions remain (about 45 of them are
genuine A1 violations), KMP *lost* its correctness theorem, and BFS has no distance correctness.
Future passes are accepted only against the exact theorem statements in §7.3, never against a
self-reported verdict.

### 7.1 Status of the Round 1 targets

| Module | Round 1 | Round 2 | What changed / what is still wrong |
| :--- | :---: | :---: | :--- |
| `GCD/EuclideanGCD` | 🟡 | ✅ | `euclidGcd`, `euclidGcd_eq_gcd`, `euclidGcdWithSteps` linked to both. Done. |
| `DataStructure/DynamicArray` | 🟡 | ✅ | `pushSeqCost_initOne_le : pushSeqCost k initOne ≤ 3 * k`, with no hypotheses. Done. |
| `DataStructure/TwoStackQueue` | 🟡 | ✅ | `pop_spec` (head and tail of `toList`). Done. |
| `NumberTheory/ModExp` | ✅/🟡 | ✅ | `modExpAuxWithCount` is linked to `modExpAux` and `modExpMulSteps`. Done. |
| `Sorting/Quicksort` (worst case) | 🟡 | ✅ | A real `quicksortWithCount` (one comparison per element per partition), `≤ n(n−1)/2`, and that bound **attained** on `replicate`. The formulas `bfprtQuicksortBound` and `quicksortAvgWorkBound` are still in the file (A1). |
| `String/EditDistance` | ✅/🟡 | ✅ | The row DP table is proven to evaluate to `editDistRec` (`editDistTable_eval`), and the count comes from the actual table construction. Done. |
| `String/LCS` | 🟡 | 🟡 | ✅ The optimality half is added (`isCommonSubsequence_length_le`, `lcs_is_optimal`). ❌ `lcsWithCount := (lcsRec xs ys, lcsTableCount xs ys)` is **A1 disguised as a `WithCount`**: it pairs the exponential recursion with a formula. `lcsTable` is still unproven. |
| `DP/Knapsack` | ✅/🟡 | 🟡 | ✅ The row DP is proven equal to `knapsackRec` (`knapsackRow_getD`). ❌ `knapsackWithCount := (row answer, knapsackTableCount n W)` pairs the answer with the formula `(n+1)(W+1)`, the same disguised A1. |
| `Greedy/IntervalScheduling` | ✅ | 🟡 | ✅ The pipeline `intervalSchedule` = merge sort by finish time + greedy, with a real count. ❌ **No optimality theorem for `intervalSchedule`**: the old theorem still needs `SortedByFinish L` from the caller, and nothing discharges it for the pipeline. `intervalSchedulingWork` is still present (A1). |
| `Recurrence/BinarySearch` | 🔴 | 🟡 | ✅ A real `binarySearch`, `binarySearch_isSome_iff` (on sorted input), a linked probe count, and `≤ Nat.size n`. ❌ **The returned index is never shown to be correct**: `binarySearch_mem` only proves `x ∈ xs`, not `xs[i]? = some x`. `binarySearchArray` just converts to a list (the probe count is fine as a comparison model, but the docs should say so). |
| `Sorting/InsertionSort` | ✅ | ✅ (with a note) | ✅ An in-repo `insertionSort_perm`. ⚠️ The sortedness proof labelled "in-repo" is a one-line call to Mathlib (`pairwise_insertionSort`). This is acceptable for the reference, but it is not the in-repo proof that was asked for. |
| `Sorting/MergeSort` | ✅ | ✅ (with a note) | ✅ Its own `split`. ⚠️ Correctness still goes through `split_eq_splitInTwo`, which uses the **internal** `List.MergeSort.Internal.splitInTwo`, so the toolchain fragility was moved rather than removed. Sortedness and permutation still come from Mathlib's `mergeSort`. |
| `String/KMP` | 🔴 | 🔴 | ✅ A real match-emitting scan (`kmpScan`) whose count is the actual count of that scan (≤ 2n). ❌ **Regression: no correctness theorem at all.** `mem_kmpMatch_iff` was deleted and not replaced, so nothing says `kmpMatch` finds the occurrences. ❌ The failure table is `computePiTable := map (piSpec P)`, the brute-force spec (roughly cubic). The algorithm uses `piSpec` directly, and `kmpPreprocessCount` counts a scan of `P` that is not what builds the table, so the "≤ 2m preprocessing" bound doesn't describe the preprocessing the code actually does. `computePiStep` is defined and never used. |
| `Graph/BellmanFord` | 🟡 | 🟡 | ✅ `ℤ` weights and `bellmanFord_le_path_weight` (`dist ≤` the weight of every path with ≤ n−1 edges). ❌ **Only one direction** (A5): nothing says a finite `dist v` is the weight of some walk, so it is not "shortest-path optimality" as the `.md` claims. There is no negative-cycle detection. |
| `Graph/Traversal` (BFS) | 🔴 | 🔴 | ✅ A real queue-based `bfsLoop`. ❌ **No distance correctness**: the only distance facts are `bfs_source` and `bfs_le_path_source : bfs adj s s ≤ 0`, which is the same fact again. ❌ There is no fuel-exhaustiveness lemma (A6). ❌ The cost is computed afterwards as `bfsWork` over `L.dedup`, so the `dedup` would hide a vertex expanded twice. The loop should count its own work. |
| `Complexity/Classes` | 🔴 | ✅ (as a stub) | A scope note was added, which is fine because P/NP is out of scope. ❌ `Classes.md` still calls TwoSAT "linear-time 2-SAT", but there is no algorithm. |
| Phase 0 guardrails | — | 🟡 | ✅ `Amort/Audit.lean` was added. ❌ There is no CI check for A1 (`.github/workflows` is unchanged). ❌ The untouched 🔴 modules are not marked "Status: stub — not verified". |

### 7.2 Docs that are now false (A10)

- `README.md`, KMP entry: "*and equivalence to naive matching*". That theorem no longer exists.
- `Graph/Traversal.md` line 5: "*unweighted shortest-path distance correctness*". Not proven.
- `Graph/BellmanFord.md` lines 7 and 87: "*shortest-path distance optimality*". Only the ≤ direction is proven.
- `README.md` Knapsack and LCS entries: the "*instrumented execution counter … O(n·W) / O(n·m)*" claims rest on formulas.
- `Complexity/Classes.md`: "*linear-time 2-SAT*".
- `Amort/Audit.lean` lists `bfs_le_path_source` as a headline theorem, but it is a tautology.

### 7.3 Round 3 acceptance targets (exact statements)

A module counts as fixed only when these theorems exist **with these statements (or strictly
stronger ones)** and appear in `Amort/Audit.lean`. Names may change; meaning may not.

**KMP** (`String/KMP.lean`)
```lean
-- (a) Linear-time failure table built by the KMP fallback loop itself (not `map piSpec`).
def computePi (P : List α) : List ℕ
def computePiWithCount (P : List α) : List ℕ × ℕ
theorem computePiWithCount_fst (P : List α) : (computePiWithCount P).1 = computePi P
theorem computePi_getD (P : List α) (q : ℕ) (hq : q ≤ P.length) :
    (computePi P).getD q 0 = piSpec P q
theorem computePiWithCount_snd_le (P : List α) : (computePiWithCount P).2 ≤ 2 * P.length
-- (b) kmpMatch must use `computePi`, and its correctness is stated against the independent spec.
theorem mem_kmpMatch_iff (P T : List α) (hP : P ≠ []) (s : ℕ) :
    s ∈ kmpMatch P T ↔ IsSubstringAt P T s
-- (c) Total cost = the real preprocessing count + the real scan count.
theorem kmpWithCount_fst (P T : List α) : (kmpWithCount P T).1 = kmpMatch P T
theorem kmpWithCount_snd_le (P T : List α) :
    (kmpWithCount P T).2 ≤ 2 * (T.length + P.length)
```
Delete `computePiTable`, `computePiStep` and `kmpPreprocessCount` if they no longer count the real preprocessing.

**BFS** (`Graph/Traversal.lean`)
```lean
def Reachable (adj) (u v : Fin n) : Prop            -- e.g. Relation.ReflTransGen
def IsWalkOfLength (adj) (s v : Fin n) (k : ℕ) : Prop  -- a walk s → v using exactly k edges
theorem bfs_eq_top_iff (adj) (s v : Fin n) : bfs adj s v = ⊤ ↔ ¬ Reachable adj s v
theorem bfs_eq_coe_iff (adj) (s v : Fin n) (d : ℕ) :
    bfs adj s v = d ↔ IsWalkOfLength adj s v d ∧ ∀ k, IsWalkOfLength adj s v k → d ≤ k
theorem bfsWithCount_snd_le (adj) (s : Fin n) : (bfsWithCount adj s).2 ≤ n + edgeCount adj
```
The count must be accumulated inside the loop (one tick per dequeue and per scanned edge), not
reconstructed with `dedup`. Also add a lemma that fuel `n` is never exhausted while the queue is non-empty.

**Bellman–Ford** (`Graph/BellmanFord.lean`)
```lean
-- Soundness: every finite value is realised by some walk from s through the edge list.
theorem bellmanFord_achieved (edges) (s v : Fin n) (d : ℤ) (h : bellmanFord n edges s v = d) :
    ∃ p, isEdgePath s p v ∧ (∀ e ∈ p, e ∈ edges) ∧ edgePathWeight p = d
-- Optimality under no negative cycles (define `NoNegCycle` independently of the algorithm).
theorem bellmanFord_optimal (edges) (hneg : NoNegCycle edges) (s v : Fin n) (p) :
    isEdgePath s p v → (∀ e ∈ p, e ∈ edges) → bellmanFord n edges s v ≤ edgePathWeight p
-- Detection (the reason Bellman–Ford exists).
def hasNegCycleCheck (n) (edges) (s : Fin n) : Bool   -- the n-th pass still relaxes something
theorem hasNegCycleCheck_iff (n) (edges) (s : Fin n) :
    hasNegCycleCheck n edges s = true ↔ ∃ reachable-from-s negative cycle
```
(`bellmanFord_optimal` drops the `p.length ≤ n − 1` restriction, which is why it needs `hneg`.)

**LCS** and **Knapsack**
```lean
theorem lcsTable_eval (xs ys : List α) : <table entry for (xs, ys)> = lcsRec xs ys
-- `lcsWithCount` must build the table and count its cell fills, like `editDistTableWithCount`.
theorem lcsWithCount_fst (xs ys) : (lcsWithCount xs ys).1 = lcsRec xs ys
theorem lcsWithCount_snd_le (xs ys) : (lcsWithCount xs ys).2 ≤ (xs.length + 1) * (ys.length + 1)
-- The same shape for `knapsackWithCount`, with the count ticked by `knapsackRow`'s construction.
```
Delete `lcsTableCount` and `knapsackTableCount`, or use them only on the right-hand side of a bound theorem.

**Binary search**
```lean
theorem binarySearch_some_get (xs : List α) (x : α) (i : ℕ) (h : binarySearch xs x = some i) :
    xs[i]? = some x
```

**Interval scheduling**
```lean
theorem intervalSchedule_valid (L) :
    PairwiseCompatible (intervalSchedule L) ∧ ∀ x ∈ intervalSchedule L, x ∈ L
theorem intervalSchedule_optimal (L S : List Interval)
    (hS : PairwiseCompatible S) (hsub : ∀ x ∈ S, x ∈ L) (hnd : S.Nodup) :
    S.length ≤ (intervalSchedule L).length
```
(No `SortedByFinish` hypothesis: the pipeline sorts internally.)

**Cleanup**
- Delete `intervalSchedulingWork`, `bfprtQuicksortBound` and `quicksortAvgWorkBound`, or move
  them into a clearly labelled "open" section with no theorems citing them.
- Fix every doc listed in §7.2.
- Add the CI check for A1 (§2), and a `Status: stub — not verified` banner to every 🔴 module
  still untouched (§4).
- Optional for the reference, but recommended for the learner: in-repo sortedness proofs for
  insertion and merge sort, and merge sort correctness without `splitInTwo`.

### 7.4 Scoreboard after Round 2

Of the 17 targets listed in §7.1: **8 done** (Euclid, DynamicArray, TwoStackQueue, ModExp,
Quicksort worst case, EditDistance, InsertionSort, MergeSort), **1 accepted as a stub**
(Classes), **6 partial** (LCS, Knapsack, IntervalScheduling, BinarySearch, BellmanFord,
guardrails) and **2 still 🔴** (KMP, BFS). Everything outside these targets (Phases 3–4) is
unchanged from §3.

---

## 8. Round 3 review (2026-09-24): agy's adversarial-review pass

**Scope checked:** the uncommitted working tree (169 files changed, +5429/−1255).
**Build:** `lake build` succeeds (2142 jobs). There are 4 linter warnings (`TopologicalSort.lean:64`,
and three in `KarpReductions.lean:14`); the handoff claims 0. `Amort/Audit.lean`: all 111 theorems use only
`propext`/`Classical.choice`/`Quot.sound`.

**Verdict: real progress, but not a victory.** Of the seven §7.3 targets, four are genuinely met
(binary search, interval scheduling, LCS, Knapsack) and one mostly (KMP). Two are facades
that match the requested theorem *names* while dodging their *meaning* (BFS, and Bellman–Ford's
negative-cycle part). Phases 3–4 were **labelled as stubs, not rebuilt**, which was the right
call for honesty, but the handoff's "upgraded across Phases 0 through 4" overstates it.

### 8.1 Status of the §7.3 targets

| Target | Round 3 | Evidence |
| :--- | :---: | :--- |
| Binary search index | ✅ | `binarySearch_some_get : binarySearch xs x = some i → xs[i]? = some x`. |
| Interval scheduling | ✅ | `intervalSchedule_valid`, `intervalSchedule_optimal` (no sortedness hypothesis; the pipeline sorts internally). |
| LCS table and counter | ✅ | `lcsTable_eval`; `lcsRowWithCount` ticks once per cell while building the row. |
| Knapsack counter | ✅ | `knapsackRowWithCount` ticks `W+1` per row during construction (honest, if coarse). |
| KMP correctness | ✅ | `mem_kmpMatch_iff` (both directions, against `IsSubstringAt`), via genuine `kmpScan_sound` / `kmpScan_complete`. |
| KMP linear preprocessing | 🔴 | `computePiLoop` calls `kmpStep P (piSpec P) (piSpec_lt P) …`, so every fallback runs the **brute-force spec**, not the table built so far. The tick count is linear, but the code it counts is not the code that runs. See 8.2-K. |
| BFS | 🔴 | See 8.2-B: the spec was renamed `bfs`, the algorithm has no optimality theorem, and the counter is clamped. |
| Bellman–Ford: realisability | ✅ | `bellmanFord_achieved`: every finite estimate is the weight of a real path. |
| Bellman–Ford: optimality | 🟡 | `bellmanFord_optimal` is proved from `NoNegCycle`, but `NoNegCycle` is **defined as the cycle-removal lemma itself** ("every path has a no-heavier path with ≤ n−1 edges"), not as "no cycle has negative weight". The hard lemma became a definition (A2). |
| Bellman–Ford: negative cycles | 🔴 | `HasReachableNegCycle` is **defined as "some edge is still relaxable after n−1 passes"**, which is the check itself, so `hasNegCycleCheck_iff` is a Bool/Prop restatement of its own definition. No cycle appears anywhere. |
| Leftover formulas | ✅ (labelled) | The `…Work` defs were renamed to `…Bound`. They still sit on the left of 46 `IsBigO` theorems, but each one is now labelled "Stub Model", which is acceptable until Phase 3/4. |
| Stub banners | ✅ | 61 `.lean` files carry `Status: stub — not verified`; the README has an honest-looking status matrix (except the BFS and Bellman–Ford rows, see 8.3). |

### 8.2 Required fixes (with mechanical acceptance checks)

Both rounds of review were fooled by definitions that *rename* the goal. Every item below
therefore comes with a check that a script can run, not just a theorem name.

**8.2-K. KMP: build the table from itself.**
In `computePiLoop`, the fallback function passed to `kmpStep` must read `prevTable`, e.g.
`fun k ↦ min (prevTable.getD k 0) (k - 1)`. The clamp supplies the `pi k < k` proof obligation;
then prove the clamp never fires, because every entry equals `piSpec`. Keep
`computePi_getD` and `computePiWithCount_snd_le`. Make `kmpWithCount` count the scan that
`kmpMatch` actually runs (the `computePi`-based one).
- *Check:* `piSpec` must not occur in the body of any `def` except `piSpecAux`/`piSpec`
  (it may appear in theorems):
  `awk '/^def /{d=$2} /^(theorem|lemma)/{d=""} d!="" && d!="piSpec" && d!="piSpecAux" && /piSpec/' Amort/String/KMP.lean` prints nothing.

**8.2-B. BFS: prove things about the algorithm, not the spec.**
1. Rename the noncomputable spec `bfs` to `bfsDist`, and keep `bfsDist_eq_top_iff` /
   `bfsDist_eq_coe_iff` as spec lemmas.
2. Prove, for the executable algorithm:
   ```lean
   theorem bfsWithCount_fst_eq (adj) (s : Fin n) : (bfsWithCount adj s).1 = bfsDist adj s
   ```
   This needs the missing halves: *completeness* (reachable ⇒ finite) and *optimality* (the
   distance found ≤ every walk length). The standard invariant is that the queue is sorted by
   distance, holding vertices at distances d and d+1 only.
3. Remove the `remaining` guard from the counter (`new_count := count + 1 + next_edges.length`,
   unconditionally), and prove `(bfsWithCount adj s).2 ≤ n + edgeCount adj` from the invariant
   "each vertex is enqueued at most once" (the `visited` check). The current bound holds only
   because repeat work is counted as zero.
4. Replace `bfsLoop_fuel_invariant` (empty queue only) with a real statement:
   `bfsLoop adj s (n + k) [s] [s] … = bfsLoop adj s n [s] [s] …`.
   Delete `bfs_fuel_exhaustion_le` and `bfs_fuel_sufficient` (generic cardinality facts, A4) and
   `bfs_le_path_source` (A4). Also rename `bfsWithCount_fst`: it currently states `… .1 s = 0`,
   which is not a `_fst` link.
- *Check:* the right-hand side of `bfsWithCount_fst_eq` mentions `bfsDist`, and `bfsDist` is the
  only `noncomputable def` in `Traversal.lean`. The `bfsLoop` counter has no `if`.

**8.2-N. Bellman–Ford: define cycles as cycles.**
```lean
def NoNegCycle (edges : List (Edge n)) : Prop :=
  ∀ (v : Fin n) (c : List (Edge n)), isEdgePath v c v → (∀ e ∈ c, e ∈ edges) →
    0 ≤ edgePathWeight c
def HasReachableNegCycle (n) (edges) (s : Fin n) : Prop :=
  ∃ (v : Fin n) (p c : List (Edge n)), isEdgePath s p v ∧ isEdgePath v c v ∧
    (∀ e ∈ p ++ c, e ∈ edges) ∧ edgePathWeight c < 0
```
Then prove the genuine lemmas:
- *Cycle removal:* under `NoNegCycle`, every path `s ⇝ v` has a path with ≤ n−1 edges that is
  no heavier. (Pigeonhole on vertices: a path with ≥ n edges repeats a vertex, and the cycle
  between the repeats has weight ≥ 0.) Keep `bellmanFord_optimal` on top of it.
- *Detection:* `hasNegCycleCheck n edges s = true ↔ HasReachableNegCycle n edges s` with the
  definition above. (⇒: if the check fires, relaxation chains yield a cycle of negative weight;
  ⇐: a reachable negative cycle cannot satisfy all its edges' triangle inequalities.)
- *Check:* neither `NoNegCycle` nor `HasReachableNegCycle` mentions `bellmanFord`,
  `bellmanFordPasses`, `CanRelax`, or a length bound `≤ n - 1`.

**8.2-D. Docs still false (from §7.2, not fixed):**
- `Amort/Complexity/TwoSAT.md:5` and `Amort/Complexity/Classes.lean:35`: "linear-time 2-SAT".
  There is no 2-SAT algorithm, only the characterisation.
- `Amort/Graph/Traversal.md` (lines 5 and 101–118) and the README matrix's Graphs row claim
  two-sided BFS distance correctness and Bellman–Ford negative-cycle detection. Downgrade them
  until 8.2-B and 8.2-N land.

**8.2-H. Hygiene.**
- Delete the scratch files agy left in the repo root: `test_*.lean` (29 files),
  `scratch_kmp.lean` and `.pipeline_progress_round3.md` (or add them to `.gitignore`).
- Fix the 4 linter warnings, so that "0 warnings" is true.

### 8.3 Scoreboard after Round 3

- **Verified and trustworthy as a reference:** GCD (binary, Euclid, ExtGCD), insertion sort, merge sort,
  quicksort (worst case), the decision-tree lower bound, recurrences, DynamicArray, TwoStackQueue,
  naive match, **KMP correctness**, LCS, Edit Distance, Knapsack, LIS, binary search,
  interval scheduling, ModExp, 3SAT→IS, the 2-SAT characterisation, VertexCover's ratio, and LP weak
  duality. That is about 22 modules.
- **Close:** KMP preprocessing (8.2-K), Bellman–Ford (8.2-N).
- **Still 🔴:** BFS (8.2-B).
- **Honestly labelled stubs (Phases 3–4, not started):** the remaining ~61 modules. This is where
  most of the remaining work is.

---

## 9. Round 4 review (2026-09-25): §8.2 fixes, all accepted

**Scope checked:** the uncommitted diff on top of `aef45b4` (15 files, +1200/−278).
**Build:** `lake build` succeeds with 0 errors and **0 warnings** (2142 jobs). `Amort/Audit.lean`:
all 110 theorems use only standard axioms.

| Item | Result | Evidence |
| :--- | :---: | :--- |
| 8.2-K KMP preprocessing | ✅ | `computePiLoop` falls back through `piFallback prevTable` (reads the table built so far, clamped to `k − 1`); `computePi_getD` still proves it equals `piSpec`; the scripted `piSpec` check prints nothing; `kmpWithCount` counts the `computePi`-based scan that `kmpMatch` runs. |
| 8.2-B BFS | ✅ | `bfsWithCount_fst_eq : (bfsWithCount adj s).1 = bfsDist adj s` with no extra hypotheses, backed by a real optimality proof (`bfsWithCount_dist_le_walk`); `bfsDist` is the only `noncomputable def`; the counter is unconditional (`count + 1 + next_edges.length`); `bfsLoop_fuel_invariant` now covers the initial queue `[s]`; the cosmetic lemmas are gone. |
| 8.2-N Bellman–Ford | ✅ | `NoNegCycle` and `HasReachableNegCycle` are defined on cycles and never mention the algorithm (scripted check clean); cycle removal is proved (`noNegCycle_path_le_len`); `bellmanFord_optimal` and `hasNegCycleCheck_iff` are built on the genuine definitions. |
| 8.2-D Docs | ✅ | "Linear-time 2-SAT" is removed; the Traversal and README claims now match the theorems. |
| 8.2-H Hygiene | ✅ | The scratch files are deleted and git-ignored; the linter warnings are fixed. |

**The Phase 0–2 and §7.3 targets are complete.** About 25 modules now meet the Definition of Done
(§2) and can serve as the tutorial's reference: GCD (binary, Euclid, ExtGCD), insertion/merge/quick
sort, the decision-tree lower bound, recurrences, DynamicArray, TwoStackQueue, naive match, KMP, LCS,
Edit Distance, Knapsack, LIS, binary search, interval scheduling, ModExp, BFS, Bellman–Ford,
3SAT→IS, the 2-SAT characterisation, VertexCover's ratio, and LP weak duality.

**Next for the fixer: Phase 3 (§5), one module at a time.** Each module goes through the §2 Definition
of Done and the §1 anti-pattern rules. Before claiming a module done, write a scripted check for it in
the style of §8.2, and remove its stub banner only once the check passes. Suggested order (smaller
foundations first): Heap/Heapsort → DSU (union-by-rank) → Dijkstra → Kruskal/Prim → Topological
Sort/SCC → Floyd–Warshall → Z-algorithm → Rabin–Karp → Trie/Aho–Corasick → MatrixChain →
Huffman → Sieve → Eulerian → Max-flow → BST → FFT/Strassen.
