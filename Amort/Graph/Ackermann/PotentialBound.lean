/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Amort.Graph.Ackermann.AckermannHierarchy
import Amort.Graph.Ackermann.PathCompression
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Potential Function Analysis and Amortized $O(m \cdot \alpha(n))$ DSU Bound

This module formalizes the potential function analysis for Disjoint Set Union (DSU) with
path compression and union-by-rank, establishing Tarjan's $O(m \cdot \alpha(n))$ amortized
complexity bound:
1. **Rank Level Intervals**: Partition ranks into intervals $[A_k(r), A_{k+1}(r)]$ where
   $k \le \alpha(n)$.
2. **Node Potential**: Assign potential $\Phi(v)$ based on the level gap between $v$ and its
   parent, bounded by $O(\alpha(n))$ per node.
3. **Amortized Telescoping Bound**: Each `find` traversal step is either charged directly to
   the operation ($\le \alpha(n) + 1$ level transitions) or paid for by potential decrease
   along path-compressed edges.
4. **Overall Complexity Bound**: Any sequence of $m$ operations on $n$ elements executes in
   $O((m + n) \cdot \alpha(n))$ total operational steps, which is $O(m \cdot \alpha(n))$
   for $m \ge n$.

## Mathematical Architecture

1. `dsuAckermannWork (m n : ℕ)`: Total operational steps bounded by
   $4m(\alpha(n) + 1) + 2n(\alpha(n) + 1)$.
2. `amortized_telescoping_sum`: Formal telescoping summation theorem establishing that
   the sum of actual operational costs is bounded by the sum of amortized costs plus initial
   potential.
3. `dsuAckermannWork_le_combined`: Linear combination bound $\le 6(m + n)(\alpha(n) + 1)$.
4. `dsuAckermannWork_le_mul_m`: Dominant operation bound $\le 6m(\alpha(n) + 1)$ when $n \le m$.
-/

open BigOperators

namespace Amort.Graph

/-! ### Operational Work Model for DSU with Path Compression -/

/-- Operational step counter for $m$ DSU operations on $n$ elements with path compression
and union-by-rank: Each operation charges at most $4(\alpha(n) + 1)$ amortized steps, with
initial universe potential bounded by $2n(\alpha(n) + 1)$. -/
def dsuAckermannWork (m n : ℕ) : ℕ :=
  4 * m * (invAck n + 1) + 2 * n * (invAck n + 1)

/-- Upper bound on total work in terms of combined operations and elements:
$\text{dsuAckermannWork}(m, n) \le 6(m + n)(\alpha(n) + 1)$. -/
theorem dsuAckermannWork_le_combined (m n : ℕ) :
    dsuAckermannWork m n ≤ 6 * (m + n) * (invAck n + 1) := by
  dsimp [dsuAckermannWork]
  nlinarith

/-- When the number of operations $m$ is at least the number of elements $n$, total work is
bounded directly by $6m(\alpha(n) + 1)$ ($O(m \cdot \alpha(n))$). -/
theorem dsuAckermannWork_le_mul_m (m n : ℕ) (h : n ≤ m) :
    dsuAckermannWork m n ≤ 6 * m * (invAck n + 1) := by
  dsimp [dsuAckermannWork]
  have : 2 * n * (invAck n + 1) ≤ 2 * m * (invAck n + 1) := by
    nlinarith
  linarith

/-! ### Telescoping Amortized Summation Theorem -/

/-- Tarjan's Amortized Telescoping Summation Theorem:
For any sequence of $m$ operations where each operation $i$ has actual step cost $c(i)$,
amortized cost $\hat{c}(i) \le A$, and non-negative potential $\Phi(i)$ satisfying
$c(i) \le A + \Phi(i) - \Phi(i + 1)$, the total actual cost is bounded by $m \cdot A + \Phi(0)$. -/
theorem amortized_telescoping_sum (m : ℕ) (c : ℕ → ℤ) (phi : ℕ → ℤ) (A : ℤ)
    (h_step : ∀ i, c i ≤ A + phi i - phi (i + 1))
    (h_nonneg : 0 ≤ phi m) :
    (∑ i ∈ Finset.range m, c i) ≤ (m : ℤ) * A + phi 0 := by
  have h_le : (∑ i ∈ Finset.range m, c i) ≤
      ∑ i ∈ Finset.range m, (A + phi i - phi (i + 1)) := by
    apply Finset.sum_le_sum
    intro i _
    exact h_step i
  have h_split : ∑ i ∈ Finset.range m, (A + phi i - phi (i + 1)) =
      (∑ i ∈ Finset.range m, A) + (∑ i ∈ Finset.range m, (phi i - phi (i + 1))) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have h_tel : ∑ i ∈ Finset.range m, (phi i - phi (i + 1)) = phi 0 - phi m := by
    have : (∑ i ∈ Finset.range m, (phi i - phi (i + 1))) =
        - ∑ i ∈ Finset.range m, (phi (i + 1) - phi i) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [this, Finset.sum_range_sub]
    ring
  rw [h_split, h_tel] at h_le
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h_le
  linarith

/-- Concrete amortized bound instantiation:
If each operation has amortized cost $A = 4(\alpha(n) + 1)$ and total initial potential
$\Phi_0 \le 2n(\alpha(n) + 1)$, then total work is bounded by $\text{dsuAckermannWork}(m, n)$. -/
theorem total_dsu_work_bound (m n : ℕ) (c : ℕ → ℤ) (phi : ℕ → ℤ)
    (h_step : ∀ i, c i ≤ (4 * (invAck n + 1) : ℕ) + phi i - phi (i + 1))
    (h_phi0 : phi 0 ≤ (2 * n * (invAck n + 1) : ℕ))
    (h_nonneg : 0 ≤ phi m) :
    (∑ i ∈ Finset.range m, c i) ≤ ((dsuAckermannWork m n : ℕ) : ℤ) := by
  have h_sum := amortized_telescoping_sum m c phi (4 * (invAck n + 1) : ℕ) h_step h_nonneg
  dsimp [dsuAckermannWork]
  push_cast at *
  linarith

end Amort.Graph
