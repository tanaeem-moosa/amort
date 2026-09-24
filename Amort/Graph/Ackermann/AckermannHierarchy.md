# The Ackermann Hierarchy and Functional Inverse Ackermann

> **Status: stub — not verified** (Phase 4 canon stub; Ackermann values are proven,
> but functional inverse is modeled as a lookup stub).


This document details the Lean 4 formalization of the Ackermann hierarchy and its functional inverse in `Amort.Graph.Ackermann.AckermannHierarchy`.

## Mathematical Definitions

### Ackermann Hierarchy
The standard two-variable Ackermann function $A : \mathbb{N} \to \mathbb{N} \to \mathbb{N}$ is defined recursively by:
- $A(0, n) = n + 1$
- $A(k + 1, 0) = A(k, 1)$
- $A(k + 1, n + 1) = A(k, A(k + 1, n))$

### Milestones and Closed Forms
1. $A(0, n) = n + 1 \implies A(0, 1) = 2$
2. $A(1, n) = n + 2 \implies A(1, 1) = 3$
3. $A(2, n) = 2n + 3 \implies A(2, 1) = 5$
4. $A(3, n) = 2^{n+3} - 3 \implies A(3, 1) = 13$
5. $A(4, 1) = A(3, 13) = 2^{16} - 3 = 65533$

### Functional Inverse Ackermann $\alpha(n)$
Defined as $\alpha(n) = \min \{ k \mid A(k, 1) \ge n \}$:
- For $n \le 2$: $\alpha(n) = 0$
- For $n \le 3$: $\alpha(n) \le 1$
- For $n \le 5$: $\alpha(n) \le 2$
- For $n \le 13$: $\alpha(n) \le 3$
- For $n \le 65533$: $\alpha(n) \le 4$

Thus for all integers up to $65533$ (and in general practical bounds), $\alpha(n) \le 4$.
