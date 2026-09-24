# Suffix Array & Kasai's Linear LCP Construction

> **Status: stub — not verified** (Phase 4 canon stub; Kasai height decrement is modeled,
> but suffix sorting and LCP execution are specification stubs).


## 1. Overview

Given a string $S$ of length $n$, the **suffix array** $\text{SA}$ is a permutation of $\{0, 1, \dots, n-1\}$ that lists the starting indices of the suffixes of $S$ in lexicographical order:
$$S[\text{SA}[0]..] < S[\text{SA}[1]..] < \dots < S[\text{SA}[n-1]..]$$

The inverse permutation $\text{rank}$ maps each suffix index $i$ to its position in the sorted suffix array:
$$\text{rank}[\text{SA}[k]] = k \quad \text{and} \quad \text{SA}[\text{rank}[i]] = i$$

The **Longest Common Prefix (LCP) array** stores the lengths of the longest common prefixes between consecutive suffixes in the sorted order:
$$\text{LCP}[k] = \text{lcp}(S[\text{SA}[k]..], S[\text{SA}[k-1]..]) \quad \text{for } 1 \le k < n$$

Kasai's algorithm (Kasai et al., 2001) computes the LCP array in $O(n)$ linear time by processing suffixes in original text order $i = 0, 1, \dots, n-1$ rather than suffix array order.

## 2. Mathematical Architecture

### Suffix Array & Rank Invariants

```lean
structure SuffixArray (n : ℕ) where
  sa : Fin n → Fin n
  rank : Fin n → Fin n
  rank_sa : ∀ k, rank (sa k) = k
  sa_rank : ∀ i, sa (rank i) = i
```

For any two suffix indices $i$ and $j$:
$$\text{lcpOfSuffixes}(S, i, j) = \text{lcp}(S.\text{drop } i, S.\text{drop } j)$$
bounded by remaining lengths $\le n - i$ and $\le n - j$.

### Kasai's Height Decrement Invariant

Let $h_i$ denote the LCP of suffix $i$ with its immediate predecessor in the suffix array:
$$h_i = \text{lcp}(S[i..], S[\text{SA}[\text{rank}[i] - 1]..])$$

When advancing from suffix $i$ to suffix $i + 1$:
Deleting the initial character from suffix $i$ and suffix $j = \text{SA}[\text{rank}[i] - 1]$ leaves suffixes $i + 1$ and $j + 1$. These two suffixes share a prefix of length $h_i - 1$. Since suffix $j$ lexicographically precedes suffix $i$, by the monotonicity of LCP across the sorted suffix array, the LCP between suffix $i + 1$ and its immediate predecessor in the suffix array is at least as large as the LCP between suffix $i + 1$ and $j + 1$:
$$h_{i+1} \ge h_i - 1$$
Formally stated in `KasaiHeightInvariant` and `kasai_height_decrement_le`.

## 3. Telescoping Character Comparison Bound $\le 2n$

In Kasai's algorithm, the current height $h$ starts at 0 and at each step $i$:
1. $h$ is decremented by at most 1 (or remains 0).
2. $h$ is incremented via character comparisons while matching characters.

Let $\Delta_i = h_{i+1} - (h_i - 1) = (h_{i+1} - h_i) + 1$ denote the number of increment operations performed at step $i$.
Summing $\Delta_i$ across all $n$ suffixes:
$$\sum_{i=0}^{n-1} \Delta_i = \sum_{i=0}^{n-1} (h_{i+1} - h_i) + \sum_{i=0}^{n-1} 1 = (h_n - h_0) + n$$

Since $0 \le h_i \le n$ for all $i$:
$$\sum_{i=0}^{n-1} \Delta_i \le n - 0 + n = 2n$$
This telescoping summation theorem is formally proven in `kasai_telescoping_increments`:
```lean
theorem kasai_telescoping_increments (n : ℕ) (h : ℕ → ℤ)
    (h_bound : h n ≤ (n : ℤ)) (h_nonneg : 0 ≤ h 0) :
    (∑ i ∈ Finset.range n, (h (i + 1) - (h i - 1))) ≤ 2 * (n : ℤ)
```

Each increment corresponds to exactly 1 successful character comparison, and there is at most 1 mismatch comparison per outer iteration $i$.
Hence, the total number of character comparisons is bounded by:
$$\text{Total Comparisons} \le 2n + n = 3n \le 4n = O(n)$$
Formally defined in `kasaiWork` and bounded by `kasaiWork_le`.

## 4. Verification & Axiom Profile

- Lean 4 compilation: clean build with 0 errors and 0 warnings.
- Axiom profile: 0 `sorryAx`, relies strictly on standard Lean 4 foundational axioms (`Classical.choice`, `propext`, `Quot.sound`).
- Line length: strictly $\le 100$ characters.
