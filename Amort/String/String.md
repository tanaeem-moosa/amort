# Textbook String Algorithms in Lean 4

This document details the Lean 4 formalization of textbook string algorithms in `Amort.String`,
contrasting naive solutions with optimal algorithms:
- **String Matching**: Naive $O(n \cdot m)$ sliding window vs. Knuth-Morris-Pratt (KMP) $O(n + m)$
  linear-time matching.
- **Sequence Alignment**: Longest Common Subsequence (LCS) and Levenshtein Edit Distance
  via bottom-up $(n + 1) \times (m + 1)$ dynamic programming tables.
- **Asymptotic Bridges**: Direct composition through `Amort.Recurrence.Composition`
  (`isBigO_nested_loops_nat` and `isBigO_sequential_add_nat`) connecting concrete step
  counters to Mathlib's `Mathlib.Analysis.Asymptotics.IsBigO` framework.

---

## 1. Architectural Overview

The formalization comprises five modular files under `Amort/String/`:

```
Amort/
├── Amort.lean                  -- Root library export
├── GCD/                        -- Stein's Binary GCD & Euclidean GCD modules
├── Sorting/                    -- Insertion Sort, Merge Sort, Decision Trees, Lower Bounds
├── Recurrence/                 -- Recurrence algebra & master theorems
└── String/
    ├── NaiveMatch.lean         -- Naive sliding-window string matching (O(n * m))
    ├── KMP.lean                -- Knuth-Morris-Pratt matching (O(n + m), potential Φ = j)
    ├── LCS.lean                -- Longest Common Subsequence DP (O(n * m))
    ├── EditDistance.lean       -- Levenshtein Edit Distance DP & minimal alignment (O(n * m))
    ├── Asymptotics.lean        -- Mathlib IsBigO bridges connecting to Amort.Recurrence
    └── String.md               -- Architectural and mathematical documentation
```

All 5 modules are fully re-exported in `Amort.lean` and compile with 0 warnings, 0 errors,
and 0 `sorryAx`.

---

## 2. String Matching: Naive vs. KMP

### 2.1 Naive Sliding-Window Matching (`NaiveMatch.lean`)

The naive string matching algorithm checks each possible shift $s \in [0, n - m]$ by
comparing characters sequentially from left to right:
- **Prefix checker**: `checkPrefix P (T.drop s)` tests whether pattern $P$ is a prefix of
  the text slice at shift $s$.
- **Step counter**: `checkPrefixCount P (T.drop s)` counts comparisons made until the first
  mismatch or complete match.
- **Shift bounds**: For each shift $s$, `checkPrefixCount P (T.drop s) ≤ P.length`
  (`checkPrefixCount_le`).
- **Total comparisons**:
  $$\text{naiveMatchCount } P\ T \le (n - m + 1) \cdot m \le n \cdot m$$
  (`naiveMatchCount_le_shifts` and `naiveMatchCount_le_mul`).
- **Correctness**:
  `s ∈ naiveMatch P T ↔ IsSubstringAt P T s` (`mem_naiveMatch_iff`), where
  `IsSubstringAt P T s ↔ s + P.length ≤ T.length ∧ (T.drop s).take P.length = P`.

### 2.2 Knuth-Morris-Pratt Algorithm (`KMP.lean`)

The KMP algorithm achieves worst-case linear time $O(n + m)$ by eliminating redundant
character comparisons through precomputed failure transitions:
- **Failure Function $\pi$**: For each prefix length $q$, `piSpec P q` computes the length of
  the longest proper prefix of $P[0..q-1]$ that is also a suffix of $P[0..q-1]$.
  - Contraction invariant: `piSpec P q < q` for all $q > 0$ (`piSpec_lt`).
- **Preprocessing Bound**: Scanning pattern $P$ against itself executes at most $2m$
  character transitions:
  $$\text{kmpPreprocessCount } P \le 2 \cdot P.\text{length} \quad (\text{kmpPreprocessCount\_le})$$
- **Potential Function Analysis for Text Scanning**:
  Define the potential function $\Phi(j) = j$, where $j \in [0, m]$ is the length of the
  currently matched prefix.
  - Single-step bound: At each character step with $k$ backtracks, $j$ decreases by at least $k$,
    and then increases by at most 1. Hence `steps + j' ≤ j + 2` (`kmpStep_bound`).
  - Telescoping across the text: Summing over all $n$ text characters telescopes:
    $$\sum_{i=1}^n (\text{steps}_i + j_i - j_{i-1}) \le 2n \implies \text{steps} + j_{\text{end}} \le j_{\text{start}} + 2n$$
    (`kmpScanCount_bound`).
  - Scanning bound starting at $j = 0$: `(kmpScanCount P pi hpi T 0).2 ≤ 2 * T.length`
    (`kmpScanCount_le_two_mul`).
- **Combined Linear Bound**:
  $$\text{kmpTotalSteps } P\ T \le 2 \cdot (n + m) \quad (\text{kmpTotalSteps\_le})$$
- **Equivalence & Correctness**:
  - `kmpMatch P T = naiveMatch P T` (`kmpMatch_eq_naiveMatch`).
  - `s ∈ kmpMatch P T ↔ IsSubstringAt P T s` (`mem_kmpMatch_iff`).

---

## 3. Sequence Alignment: Dynamic Programming

### 3.1 Longest Common Subsequence (`LCS.lean`)

The LCS problem computes the maximum length of a common subsequence between sequences $xs$ and $ys$:
- **Recursive Formulation**:
  ```lean
  def lcsRec : List α → List α → ℕ
    | [], _ => 0
    | _, [] => 0
    | x :: xs, y :: ys =>
      if x = y then 1 + lcsRec xs ys
      else max (lcsRec (x :: xs) ys) (lcsRec xs (y :: ys))
  ```
- **Constructive Correctness**:
  `lcsWitness xs ys` explicitly extracts a common subsequence from the decisions of `lcsRec`:
  - `(lcsWitness xs ys).Sublist xs` (`lcsWitness_sublist_left`).
  - `(lcsWitness xs ys).Sublist ys` (`lcsWitness_sublist_right`).
  - `(lcsWitness xs ys).length = lcsRec xs ys` (`lcsWitness_length`).
  - Maximal length existence: `∃ s, IsCommonSubsequence s xs ys ∧ s.length = lcsRec xs ys`
    (`lcs_is_maximal`).
  - Identity: `lcsRec s s = s.length` (`lcsRec_self`).
- **Bottom-Up DP Table**:
  `lcsTable xs ys` computes the $(n + 1) \times (m + 1)$ dynamic programming table row by row:
  - Row count: `(lcsTable xs ys).length = xs.length + 1` (`lcsTable_length`).
  - Operational step count:
    $$\text{lcsTableCount } xs\ ys = (n + 1) \cdot (m + 1) \le (n + 1) \cdot (m + 1)$$
    (`lcsTableCount_eq` and `lcsTableCount_le`).

### 3.2 Edit Distance (`EditDistance.lean`)

Levenshtein edit distance measures the minimum cost of transforming $xs$ into $ys$ using
substitutions (cost 0 if matching, 1 if mismatch), deletions (cost 1), and insertions (cost 1):
- **Alignment Model**:
  Inductive predicate `IsAlignment ops xs ys` specifies sequences of `EditOp α` operations
  transforming $xs$ into $ys$, with total cost `alignmentCost ops = (ops.map opCost).sum`.
- **Recursive Formulation**:
  ```lean
  def editDistRec : List α → List α → ℕ
    | [], ys => ys.length
    | xs, [] => xs.length
    | x :: xs, y :: ys =>
      let cost_sub := (if x = y then 0 else 1) + editDistRec xs ys
      let cost_del := 1 + editDistRec xs (y :: ys)
      let cost_ins := 1 + editDistRec (x :: xs) ys
      min cost_sub (min cost_del cost_ins)
  ```
- **Minimal Cost Alignment Correctness**:
  - Soundness: Any valid alignment has cost at least `editDistRec`:
    $$\forall \text{ops},\ \text{IsAlignment ops } xs\ ys \implies \text{editDistRec } xs\ ys \le \text{alignmentCost ops}$$
    (`editDistRec_le_alignmentCost`).
  - Completeness: `editDistWitness xs ys` constructs an alignment achieving exactly `editDistRec`:
    $$\text{IsAlignment (editDistWitness } xs\ ys)\ xs\ ys \wedge \text{alignmentCost (editDistWitness } xs\ ys) = \text{editDistRec } xs\ ys$$
    (`editDistWitness_isAlignment` and `editDistWitness_cost`).
  - Minimality theorem: `editDist_is_minimal_alignment`.
- **Bottom-Up DP Matrix**:
  `editDistTable xs ys` computes the $(n + 1) \times (m + 1)$ matrix row by row:
  - Row count: `(editDistTable xs ys).length = xs.length + 1` (`editDistTable_length`).
  - Operational step count:
    $$\text{editDistTableCount } xs\ ys = (n + 1) \cdot (m + 1) \le (n + 1) \cdot (m + 1)$$
    (`editDistTableCount_eq` and `editDistTableCount_le`).

---

## 4. Asymptotics & Composition Bridges (`Asymptotics.lean`)

All algorithmic step bounds connect directly to Mathlib's `Mathlib.Analysis.Asymptotics.IsBigO`
via the compositional theorems in `Amort.Recurrence.Composition`.

### 4.1 Product Composition for 2D DP Tables
Because $n + 1 = O(n)$ (`isBigO_fst_add_one_atTop`) and $m + 1 = O(m)$ (`isBigO_snd_add_one_atTop`)
under `Filter.atTop` on $\mathbb{N} \times \mathbb{N}$, applying `isBigO_nested_loops_nat` yields:
$$(n + 1) \cdot (m + 1) = O(n \cdot m) \quad (\text{isBigO\_succ\_mul\_succ\_atTop})$$
Consequently:
- `isBigO_lcsTableCount_atTop`: LCS DP table size is $O(n \cdot m)$.
- `isBigO_editDistTableCount_atTop`: Edit Distance DP matrix size is $O(n \cdot m)$.
- `isBigO_naiveMatch_bound_atTop`: Naive string matching worst-case comparisons are $O(n \cdot m)$.

### 4.2 Sequential Sum Composition for KMP
KMP text scanning executes in $2n = O(n)$ (`isBigO_two_mul_fst_atTop`) and preprocessing
executes in $2m = O(m)$ (`isBigO_two_mul_snd_atTop`).
Applying `isBigO_sequential_add_nat` yields:
$$2n + 2m = O(n + m) \quad (\text{isBigO\_kmp\_linear\_atTop})$$
$$2(n + m) = O(n + m) \quad (\text{isBigO\_kmpTotalSteps\_bound\_atTop})$$

---

## 5. Comparison Tables

### 5.1 String Matching: Naive vs. Knuth-Morris-Pratt

| Algorithm | Preprocessing Time | Search Comparisons | Combined Bound | Asymptotic Class | Method |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **Naive Matching** | $0$ | $\le (n - m + 1) \cdot m$ | $\le n \cdot m$ | $O(n \cdot m)$ | Sliding window |
| **KMP Matching** | $\le 2m$ | $\le 2n$ | $\le 2(n + m)$ | $O(n + m)$ | Failure $\pi$ + Potential $\Phi = j$ |

### 5.2 Sequence Alignment: LCS vs. Edit Distance

| Problem | Table Dimensions | Cell Operations | Total Operations | Asymptotic Class | Correctness Target |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **LCS** | $(n + 1) \times (m + 1)$ | Match / Max | $\le (n + 1)(m + 1)$ | $O(n \cdot m)$ | Maximal common subsequence |
| **Edit Distance** | $(n + 1) \times (m + 1)$ | Sub / Ins / Del | $\le (n + 1)(m + 1)$ | $O(n \cdot m)$ | Minimal cost alignment |

---

## 6. Verification & Axiom Audit

Every declaration in `Amort.String` has been verified via `#print axioms`.
The formalization relies strictly on standard foundational Lean 4 axioms:
- `propext` (Propositional Extensionality)
- `Classical.choice` (Axiom of Choice)
- `Quot.sound` (Quotient Soundness)

Zero theorems rely on `sorry` or `sorryAx`.
