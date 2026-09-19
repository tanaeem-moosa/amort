# Asymptotic Complexity Bridges for Advanced String Algorithms

## 1. Overview

This module formalizes the mathematical connection between concrete operational step models of advanced string algorithms and Mathlib's asymptotic complexity framework `Mathlib.Analysis.Asymptotics.IsBigO` under `Filter.atTop`.

Algorithms covered:
1. **Prefix Trie**: Dictionary construction $\sum_{i=1}^k |P_i| = O\left(\sum_{i=1}^k |P_i|\right)$.
2. **Aho-Corasick Automaton**:
   - Text scanning: $2|T| = O(|T|)$.
   - Full multi-pattern search: $\sum |P_i| + 2|T| + z = O(\sum |P_i| + |T| + z)$.
3. **Gusfield's Z-Algorithm**: Character comparisons $2|S| = O(|S|)$.
4. **Rabin-Karp String Matching**: Average-case operational work $2(|T| + |P|) = O(|T| + |P|)$.
5. **Suffix Array & Kasai's LCP Construction**: Character comparisons $2n = O(n)$.

## 2. Mathematical Theorems

### Trie Dictionary Construction Asymptotics

```lean
theorem isBigO_trieBuildWork_atTop :
    (fun (p : ℕ) ↦ ((p : ℕ) : ℝ)) =O[Filter.atTop]
      (fun p ↦ ((p : ℕ) : ℝ))
```

### Aho-Corasick Multi-Pattern Search Asymptotics

```lean
theorem isBigO_acScan_atTop :
    (fun (n : ℕ) ↦ ((2 * n : ℕ) : ℝ)) =O[Filter.atTop]
      (fun n ↦ ((n : ℕ) : ℝ))

theorem isBigO_acTotalSearchWork_atTop :
    (fun (p : (ℕ × ℕ) × ℕ) ↦
        (((AhoCorasick.acTotalSearchWork p.1.1 p.1.2 p.2 : ℕ) : ℝ))) =O[Filter.atTop]
      (fun p ↦ (((p.1.1 + p.1.2 + p.2 : ℕ) : ℝ)))
```

### Gusfield's Z-Algorithm Asymptotics

```lean
theorem isBigO_zAlgorithmWork_atTop :
    (fun (n : ℕ) ↦ (((zAlgorithmWork n : ℕ) : ℝ))) =O[Filter.atTop]
      (fun n ↦ ((n : ℕ) : ℝ))
```

### Rabin-Karp String Matching Asymptotics

```lean
theorem isBigO_rabinKarpAverageWork_atTop :
    (fun (p : ℕ × ℕ) ↦ (((rabinKarpAverageWork p.1 p.2 : ℕ) : ℝ))) =O[Filter.atTop]
      (fun p ↦ (((p.1 + p.2 : ℕ) : ℝ)))
```

### Suffix Array and Kasai's LCP Asymptotics

```lean
theorem isBigO_kasaiWork_atTop :
    (fun (n : ℕ) ↦ (((kasaiWork n : ℕ) : ℝ))) =O[Filter.atTop]
      (fun n ↦ ((n : ℕ) : ℝ))
```

## 3. Verification & Axiom Profile

- Lean 4 compilation: clean build with 0 errors and 0 warnings.
- Axiom profile: 0 `sorryAx`, relies strictly on standard Lean 4 foundational axioms (`Classical.choice`, `propext`, `Quot.sound`).
- Line length: strictly $\le 100$ characters.
