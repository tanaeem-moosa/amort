# Asymptotic Complexity of Ukkonen's Suffix Tree Construction

This document details the asymptotic complexity bridges in `Amort.String.SuffixTree.Asymptotics` connecting Ukkonen's operational step bounds to Mathlib's `Asymptotics.IsBigO` under `Filter.atTop` on $\mathbb{N}$.

## Theorems
- `isBigO_ukkonenWork_atTop`: Total work of Ukkonen's suffix tree construction is $O(n)$ in `IsBigO`.

## Proof Architecture
1. Operational step counter `ukkonenWork n = 4 * n`.
2. Asymptotic bound via `IsBigO.of_bound` with explicit constant $C = 4$.
