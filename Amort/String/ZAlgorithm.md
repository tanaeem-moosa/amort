# Gusfield's Z-Algorithm

## 1. Overview

Gusfield's Z-Algorithm (Gusfield, 1997) is a fundamental linear-time string matching and preprocessing technique. Given a string $S$ of length $n$, it computes the $Z$-array:
$$Z[i] = \text{LCP}(S, S[i..]) \quad \text{for } 0 \le i < n$$
where $\text{LCP}(u, v)$ is the length of the longest common prefix of strings $u$ and $v$.

The algorithm maintains a rightmost match window $[l, r]$ (known as the rightmost $Z$-box), maximizing $r$, such that $S[l \dots r]$ matches prefix $S[0 \dots r - l]$.

## 2. Mathematical Architecture

### Longest Common Prefix (LCP) Foundation

The recursive character comparison model:
$$\text{lcp}(\varepsilon, ys) = 0$$
$$\text{lcp}(x \cdot xs, y \cdot ys) = \begin{cases} 1 + \text{lcp}(xs, ys) & \text{if } x = y \\ 0 & \text{if } x \ne y \end{cases}$$

Key structural theorems proven:
- Boundedness: $\text{lcp}(xs, ys) \le |xs|$ and $\text{lcp}(xs, ys) \le |ys|$.
- Additivity: $\text{lcp}(P ++ xs, P ++ ys) = |P| + \text{lcp}(xs, ys)$.
- Prefix Equivalence: $\text{lcp}(P ++ xs, ys) \ge |P| \iff P <+: ys$.

### Window Maintenance and Two-Case Branch Logic

Let $i \ge 1$ be the current index. The algorithm inspects the current window $[l, r]$:

1. **Case 1: $i > r$ (Outside Current Window)**
   Compute $Z[i]$ by explicit character comparisons starting from $S[0]$ and $S[i]$. If $Z[i] > 0$, initialize a new rightmost window $[l, r] = [i, i + Z[i] - 1]$.

2. **Case 2: $i \le r$ (Inside Current Window)**
   Let $k = i - l$ be the corresponding prefix position, and let $\beta = r - i + 1$ be the remaining length of the current $Z$-box.
   - **Subcase 2a: $Z[k] < \beta$**
     The match does not reach the right boundary $r$. By substring equality $S[i \dots r] = S[k \dots r - l]$, $Z[i] = Z[k]$ immediately with **0 character comparisons**. Window $[l, r]$ remains unchanged.
   - **Subcase 2b: $Z[k] \ge \beta$**
     At least $\beta$ characters are guaranteed to match. Character comparisons resume strictly beyond $r$, comparing $S[\beta + q]$ with $S[r + 1 + q]$. If the match extends by $q \ge 0$ characters, the window advances to $[l', r'] = [i, r + q]$.

## 3. Linear Comparison Bound $\le 2|S|$

The linear execution time $O(|S|)$ follows from the **window expansion progress invariant**:
1. **Successful Comparisons**: Every character comparison that results in an equality match strictly advances the rightmost window boundary $r$. Since $r$ starts at 0 and cannot exceed $n = |S|$, the total number of successful comparisons across the entire algorithm is $\le n$.
2. **Mismatch Comparisons**: In each iteration $i \in [1, n)$, at most one character comparison can result in a mismatch (terminating the while-loop). Thus, the total number of mismatch comparisons is $\le n - 1$.

Summing both components:
$$\text{Total Comparisons} \le \text{Successful} + \text{Mismatches} \le n + n = 2n$$
Formally defined in `zAlgorithmWork` and bounded by `zAlgorithmWork_le`.

## 4. Pattern Matching Reduction: $Z(P \$ T)$

Exact string matching of pattern $P$ in text $T$ reduces directly to computing the $Z$-array on the concatenated string:
$$S = P ++ [\$] ++ T$$
where $\$$ is a sentinel delimiter character not appearing in $P$ or $T$.

For any shift $j \in [0, |T| - |P|]$:
$$Z(S)[|P| + 1 + j] \ge |P| \iff P <+: T.\text{drop } j \iff \text{IsSubstringAt } P \; T \; j$$
This reduction is formally proven in `z_pattern_match_iff_prefix` and `z_pattern_match_iff_substring`.

## 5. Verification & Axiom Profile

- Lean 4 compilation: clean build with 0 errors and 0 warnings.
- Axiom profile: 0 `sorryAx`, relies strictly on standard Lean 4 foundational axioms (`Classical.choice`, `propext`, `Quot.sound`).
- Line length: strictly $\le 100$ characters.
