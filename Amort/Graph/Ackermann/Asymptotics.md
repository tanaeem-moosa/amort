# Asymptotic Complexity of DSU with Path Compression

This document details the asymptotic complexity bridges in `Amort.Graph.Ackermann.Asymptotics` connecting the operational step bounds for DSU with path compression to Mathlib's `Asymptotics.IsBigO` under `Filter.atTop` on $\mathbb{N} \times \mathbb{N}$.

## Theorems
- `isBigO_dsuAckermannWork_atTop`: Total work across $m$ operations on $n$ elements is $O((m + n)(\alpha(n) + 1))$.

## Proof Architecture
1. Step counter `dsuAckermannWork m n = 4 * m * (invAck n + 1) + 2 * n * (invAck n + 1)`.
2. Asymptotic bound via `IsBigO.of_bound` with explicit constant $C = 6$.
