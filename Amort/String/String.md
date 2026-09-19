# Textbook String Algorithms in Lean 4

This document details the Lean 4 formalization of foundational and advanced textbook string
algorithms in `Amort.String`:
- **Single-Pattern Matching**: Naive $O(n \cdot m)$ sliding window vs. Knuth-Morris-Pratt (KMP)
  $O(n + m)$ linear-time matching.
- **Multi-Pattern Matching & Dictionaries**:
  - Prefix Trie (`Amort/String/Trie.lean`, `Trie.md`): explicit root, child transitions, word
    termination markers, retrieval soundness, and $O(\sum |P_i|)$ dictionary construction.
  - Aho-Corasick Multi-Pattern Automaton (`Amort/String/AhoCorasick.lean`, `AhoCorasick.md`):
    failure links, text scanning state transitions, $\Phi(u) = \text{depth}(u)$ potential function
    proving $\le 2|T|$ scanning steps, and overall $O(\sum |P_i| + |T| + z)$ search complexity.
- **Linear Pattern Analysis**:
  - Gusfield's Z-Algorithm (`Amort/String/ZAlgorithm.lean`, `ZAlgorithm.md`): $Z$-array
    $Z[i] = \text{LCP}(S, S[i..])$, rightmost match window $[l, r]$, two-case branch logic,
    $\le 2|S|$ comparison bound via window expansion progress, and pattern matching reduction $Z(P \$ T)$.
- **Algebraic / Fingerprinting Matching**:
  - Rabin-Karp Algorithm (`Amort/String/RabinKarp.lean`, `RabinKarp.md`): polynomial rolling hash,
    $O(1)$ sliding window update identity, hash congruence soundness, and average-case
    $O(|T| + |P|)$ search complexity.
- **Suffix Structures & Linear LCP**:
  - Suffix Array & Kasai's LCP (`Amort/String/SuffixArray.lean`, `SuffixArray.md`): suffix orderings,
    inverse permutation ranks, Kasai's height decrement invariant $h_{i+1} \ge h_i - 1$, and
    telescoping $\le 2n$ comparison bound yielding $O(n)$ step complexity.
- **Sequence Alignment**: Longest Common Subsequence (LCS) and Levenshtein Edit Distance
  via bottom-up $(n + 1) \times (m + 1)$ dynamic programming tables.
- **Asymptotic Bridges**: Direct connections to Mathlib's `Mathlib.Analysis.Asymptotics.IsBigO`
  under `Filter.atTop` (`Asymptotics.lean` and `AdvancedAsymptotics.lean`).

---

## 1. Architectural Overview

The formalization comprises eleven modular files under `Amort/String/`:

```
Amort/String/
├── NaiveMatch.lean         -- Naive sliding-window string matching (O(n * m))
├── KMP.lean                -- Knuth-Morris-Pratt matching (O(n + m), potential Φ = j)
├── LCS.lean                -- Longest Common Subsequence DP (O(n * m))
├── EditDistance.lean       -- Levenshtein Edit Distance DP & minimal alignment (O(n * m))
├── Trie.lean               -- Prefix trie dictionary data structure (O(∑|P_i|))
├── AhoCorasick.lean        -- Aho-Corasick automaton (O(∑|P_i| + |T| + z))
├── ZAlgorithm.lean         -- Gusfield's Z-Algorithm (O(|S|), window expansion progress)
├── RabinKarp.lean          -- Rabin-Karp rolling hash matching (O(|T| + |P|))
├── SuffixArray.lean        -- Suffix Array and Kasai's linear LCP (O(n), invariant h_{i+1} ≥ h_i - 1)
├── Asymptotics.lean        -- Mathlib IsBigO bridges for basic matching & DP
├── AdvancedAsymptotics.lean-- Mathlib IsBigO bridges for Trie, AC, Z, RK, and Kasai
└── String.md               -- Consolidated architectural documentation
```

All 11 modules are exported in `Amort.lean` and compile with 0 warnings, 0 errors, and 0 `sorryAx`.

---

## 2. Advanced Multi-Pattern Matching: Trie & Aho-Corasick

### 2.1 Prefix Trie Dictionary (`Trie.lean`)
- **Automaton Model**: `Trie α` structure specifying `numNodes`, `root`, transition `step`,
  termination marker `isTerminal`, and tree depth invariant `depth`.
- **Prefix-Tree Walk**: `walk t u w` traces transitions along word `w`.
- **Depth Invariant**: `walk t u w = some v → depth v = depth u + w.length`.
- **Retrieval Soundness**:
  $$\text{contains}(w) = \text{true} \iff \exists v, \; \text{walk}(\text{root}, w) = \text{some } v \land \text{isTerminal}(v) = \text{true}$$
- **Operational Bounds**:
  - Single-word lookup: bounded by $|w|$ edge traversals (`lookupSteps_le`).
  - Single-word insert: bounded by $|w|$ operations (`insertWork_le`).
  - Dictionary construction: bounded by $\sum |P_i|$ (`buildWork_eq_sum`).

### 2.2 Aho-Corasick Automaton (`AhoCorasick.lean`)
- **Structure**: Extends prefix trie with failure links `fail : ℕ → ℕ` and dictionary `outputList`.
- **Depth Contraction Invariant**: $\forall u, \; \text{depth}(u) > 0 \implies \text{depth}(\text{fail}(u)) < \text{depth}(u)$.
- **State Transition**: `acStep` follows trie transitions when available; falls back along `fail(u)` otherwise.
- **Potential Function Analysis**: With $\Phi(u) = \text{depth}(u)$:
  $$\text{steps} + \Phi(u') \le \Phi(u) + 2 \quad (\text{acStep\_bound})$$
- **Linear Text Scanning**: Summing across text $T$ from root telescopes:
  $$\text{Total Steps} \le 2|T| \quad (\text{acScan\_le\_two\_mul})$$
- **Total Search Complexity**:
  $$\text{Total Work} \le \sum_{i=1}^k |P_i| + 2|T| + z = O\left(\sum_{i=1}^k |P_i| + |T| + z\right)$$

---

## 3. Gusfield's Z-Algorithm (`ZAlgorithm.lean`)

- **$Z$-Array Specification**: $Z[i] = \text{lcp}(S, S.\text{drop } i)$ (`zSpec`).
- **Rightmost Window $[l, r]$**:
  - Case 1 ($i > r$): Explicit comparisons starting from 0, initializing new window.
  - Case 2 ($i \le r$): Let $k = i - l$ and $\beta = r - i + 1$:
    - Subcase 2a ($Z[k] < \beta$): Exact reuse $Z[i] = Z[k]$ with 0 comparisons.
    - Subcase 2b ($Z[k] \ge \beta$): Comparisons strictly beyond $r$, expanding window.
- **Linear Bound**: Every successful comparison increases $r$ ($\le n$ steps); at most 1 mismatch
  per position ($\le n$ steps). Total comparisons $\le 2|S|$ (`zAlgorithmWork_le`).
- **Pattern Matching Reduction**:
  $$Z(P \$ T)[|P| + 1 + j] \ge |P| \iff P <+: T.\text{drop } j \iff \text{IsSubstringAt } P \; T \; j$$

---

## 4. Rabin-Karp Rolling Hash (`RabinKarp.lean`)

- **Polynomial Rolling Hash**: $H(w) = \sum_{j=0}^{m-1} w[j] \cdot B^{m - 1 - j}$ (`polyHash`).
- **Sliding Window Identity**:
  $$H(S[i+1 \dots i+m]) \equiv (H(S[i \dots i+m-1]) \cdot B - S[i] \cdot B^m + S[i+m]) \pmod p$$
  Formally proven in `polyHash_sliding_window` and `polyHash_sliding_window_mod`.
- **Soundness**: Identical substrings produce identical hash values (`polyHash_congruence_soundness`).
- **Complexity**: Average-case operational work bounded by $2(|T| + |P|)$ (`rabinKarpWork_no_collisions`).

---

## 5. Suffix Array & Kasai's LCP (`SuffixArray.lean`)

- **Suffix Array Permutation**: Permutation `sa : Fin n → Fin n` and rank `rank : Fin n → Fin n` (`SuffixArray`).
- **Height Decrement Invariant**:
  $$h_{i+1} \ge h_i - 1 \quad \text{where } h_i = \text{LCP}(S[i..], S[\text{SA}[\text{rank}[i] - 1]..])$$
  Formally verified in `KasaiHeightInvariant` and `kasai_height_decrement_le`.
- **Telescoping Comparison Bound**:
  $$\sum_{i=0}^{n-1} (h_{i+1} - (h_i - 1)) = (h_n - h_0) + n \le 2n$$
  Formally proven in `kasai_telescoping_increments`, establishing linear operational complexity
  $\le 2n$ (`kasaiWork_le`).

---

## 6. Asymptotic Complexity Summary (`AdvancedAsymptotics.lean`)

| Algorithm | Concrete Bound | Asymptotic Class (`IsBigO`) | Lean Theorem |
| :--- | :--- | :--- | :--- |
| **Prefix Trie Build** | $\sum |P_i|$ | $O(\sum |P_i|)$ | `isBigO_trieBuildWork_atTop` |
| **Aho-Corasick Scan** | $\le 2|T|$ | $O(|T|)$ | `isBigO_acScan_atTop` |
| **Aho-Corasick Search**| $\sum |P_i| + 2|T| + z$ | $O(\sum |P_i| + |T| + z)$ | `isBigO_acTotalSearchWork_atTop` |
| **Gusfield's Z-Alg** | $\le 2|S|$ | $O(|S|)$ | `isBigO_zAlgorithmWork_atTop` |
| **Rabin-Karp Match** | $\le 2(|T| + |P|)$ | $O(|T| + |P|)$ | `isBigO_rabinKarpAverageWork_atTop` |
| **Kasai's LCP** | $\le 2n$ | $O(n)$ | `isBigO_kasaiWork_atTop` |

---

## 7. Verification & Axiom Audit

All milestone theorems in `Amort.String` depend exclusively on standard Lean 4 foundational axioms:
- `propext`
- `Classical.choice`
- `Quot.sound`

Verified with 0 `sorry` and 0 `sorryAx`.
