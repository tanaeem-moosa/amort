# Suffix Trees & Ukkonen's Online Linear-Time Construction (`Amort.String.SuffixTree`)

This directory formalizes Compact Suffix Trees and Ukkonen's online linear-time construction
algorithm in Lean 4:

1. **Compact Suffix Tree Structure**:
   - Edge labels as slice intervals $[l, r]$ into text $S$, taking $O(1)$ space per edge.
   - Branching property: all internal nodes have out-degree $\ge 2$.
   - Structural size theorems:
     - At most $n$ leaves.
     - At most $n - 1$ internal branching nodes (by tree combinatorics $2I \le L + I - 1 \implies I \le L - 1$).
     - Total nodes $L + I \le 2n - 1 \le 2n$.

2. **Suffix Links**:
   - Suffix link mapping each internal node representing $a \beta$ to internal node representing $\beta$.
   - String depth invariant: $\text{stringDepth}(\text{link}(u)) = \text{stringDepth}(u) - 1$.
   - Strictly decreasing depth and chain termination bound $\le n$ steps.

3. **Ukkonen's Online Algorithm & $O(n)$ Bound**:
   - Active point `(active_node, active_edge, active_len)`.
   - Three extension rules: Rule 1 (leaf extension), Rule 2 (branching split), Rule 3 (extension stop).
   - Global end pointer $e$ extends all existing leaves in $O(1)$ amortized time.
   - Suffix link traversals bound total splits to $\le 2n$.
   - Operational work model $\text{ukkonenWork}(n) = 4n$, establishing $O(n)$ linear time.

4. **Asymptotic Complexity Bridges**:
   - Bridge to Mathlib's `Mathlib.Analysis.Asymptotics.IsBigO` under `Filter.atTop` on $\mathbb{N}$.

## Module Map
- `Amort.String.SuffixTree.CompactTree`: `Amort/String/SuffixTree/CompactTree.lean`
- `Amort.String.SuffixTree.SuffixLink`: `Amort/String/SuffixTree/SuffixLink.lean`
- `Amort.String.SuffixTree.Ukkonen`: `Amort/String/SuffixTree/Ukkonen.lean`
- `Amort.String.SuffixTree.Asymptotics`: `Amort/String/SuffixTree/Asymptotics.lean`
