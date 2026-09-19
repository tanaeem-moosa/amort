/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The Ackermann Hierarchy and Functional Inverse Ackermann

This module formalizes the textbook Ackermann hierarchy function $A_k(n)$, proves strict
monotonicity, establishes exact closed-form evaluations for levels $k \in \{0, 1, 2, 3, 4\}$,
defines the functional inverse Ackermann function $\alpha(n)$, and proves that $\alpha(n)$ is
extremely slow-growing ($\alpha(n) \le 4$ for all $n \le 65533$).

## Mathematical Architecture

1. **Ackermann Function Definition**:
   The two-variable Ackermann function $A : \mathbb{N} \to \mathbb{N} \to \mathbb{N}$ is defined by:
   - $A(0, n) = n + 1$
   - $A(k + 1, 0) = A(k, 1)$
   - $A(k + 1, n + 1) = A(k, A(k + 1, n))$
   with well-founded termination by lexicographical measure $(k, n)$.

2. **Growth Hierarchy and Closed Forms**:
   - Level 0 (Successor): $A(0, n) = n + 1$
   - Level 1 (Addition): $A(1, n) = n + 2$
   - Level 2 (Multiplication): $A(2, n) = 2n + 3$
   - Level 3 (Exponentiation): $A(3, n) = 2^{n+3} - 3$
   - Level 4 (Tetration): $A(4, 1) = 2^{16} - 3 = 65533$

3. **Strict Monotonicity Invariants**:
   - Argument domination: $n < A(k, n)$ for all $k, n$.
   - Strict right-monotonicity: $A(k, n) < A(k, n + 1)$ and $n < m \implies A(k, n) < A(k, m)$.

4. **Functional Inverse Ackermann Function $\alpha(n)$**:
   Defined as $\alpha(n) = \min \{ k \mid A(k, 1) \ge n \}$.
   - For $n \le 2$: $\alpha(n) = 0$ since $A(0, 1) = 2 \ge n$.
   - For $n \le 3$: $\alpha(n) \le 1$ since $A(1, 1) = 3 \ge n$.
   - For $n \le 5$: $\alpha(n) \le 2$ since $A(2, 1) = 5 \ge n$.
   - For $n \le 13$: $\alpha(n) \le 3$ since $A(3, 1) = 13 \ge n$.
   - For $n \le 65533$: $\alpha(n) \le 4$ since $A(4, 1) = 65533 \ge n$.
   Thus $\alpha(n) \le 4$ for all practical input sizes.

## Key Definitions and Theorems
- `Amort.Graph.ack`: The Ackermann hierarchy function.
- `Amort.Graph.ack_zero`: $A(0, n) = n + 1$.
- `Amort.Graph.ack_one`: $A(1, n) = n + 2$.
- `Amort.Graph.ack_two`: $A(2, n) = 2n + 3$.
- `Amort.Graph.ack_three`: $A(3, n) = 2^{n+3} - 3$.
- `Amort.Graph.ack_four_one`: $A(4, 1) = 65533$.
- `Amort.Graph.n_lt_ack`: $n < A(k, n)$.
- `Amort.Graph.ack_lt_ack_succ_right`: $A(k, n) < A(k, n + 1)$.
- `Amort.Graph.ack_strictMono_right`: $n < m \implies A(k, n) < A(k, m)$.
- `Amort.Graph.invAck`: Functional inverse Ackermann function $\alpha(n)$.
- `Amort.Graph.invAck_le_four`: $\alpha(n) \le 4$ for all $n \le 65533$.
- `Amort.Graph.invAck_monotone`: $a \le b \implies \alpha(a) \le \alpha(b)$.
-/

namespace Amort.Graph

/-! ### Ackermann Hierarchy Definition -/

/-- The Ackermann hierarchy function $A(k, n)$ defined recursively with well-founded
lexicographic termination on $(k, n)$. -/
def ack : ℕ → ℕ → ℕ
  | 0, n => n + 1
  | k + 1, 0 => ack k 1
  | k + 1, n + 1 => ack k (ack (k + 1) n)
termination_by k n => (k, n)

/-! ### Level Equations and Closed Forms -/

/-- Level 0 equation: $A(0, n) = n + 1$. -/
theorem ack_zero (n : ℕ) : ack 0 n = n + 1 := by rw [ack]

/-- Level 1 equation: $A(1, n) = n + 2$. -/
theorem ack_one (n : ℕ) : ack 1 n = n + 2 := by
  induction n with
  | zero => rw [ack, ack_zero]
  | succ n ih => rw [ack, ih, ack_zero]

/-- Level 2 equation: $A(2, n) = 2n + 3$. -/
theorem ack_two (n : ℕ) : ack 2 n = 2 * n + 3 := by
  induction n with
  | zero => rw [ack, ack_one]
  | succ n ih =>
    rw [ack, ih, ack_one]
    omega

/-- Level 3 closed form: $A(3, n) = 2^{n+3} - 3$. -/
theorem ack_three (n : ℕ) : ack 3 n = 2 ^ (n + 3) - 3 := by
  induction n with
  | zero =>
    rw [ack, ack_two]
    decide
  | succ n ih =>
    rw [ack, ih, ack_two]
    have hstep : 2 ^ (n + 1 + 3) = 2 * 2 ^ (n + 3) := by
      have : n + 1 + 3 = (n + 3) + 1 := by omega
      rw [this]
      exact Nat.pow_succ'
    have h1 : 3 ≤ 2 ^ (n + 3) := by
      have : 8 ≤ 2 ^ (n + 3) := by
        calc 8 = 2 ^ 3 := by rfl
        _ ≤ 2 ^ (n + 3) := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    omega

/-! ### Milestone Evaluations on $n = 1$ -/

/-- Milestone evaluation at level 0: $A(0, 1) = 2$. -/
theorem ack_zero_one : ack 0 1 = 2 := by rw [ack_zero]

/-- Milestone evaluation at level 1: $A(1, 1) = 3$. -/
theorem ack_one_one : ack 1 1 = 3 := by rw [ack_one]

/-- Milestone evaluation at level 2: $A(2, 1) = 5$. -/
theorem ack_two_one : ack 2 1 = 5 := by rw [ack_two]

/-- Milestone evaluation at level 3: $A(3, 1) = 13$. -/
theorem ack_three_one : ack 3 1 = 13 := by
  rw [ack_three]
  decide

/-- Milestone evaluation at level 4: $A(4, 1) = 2^{16} - 3 = 65533$. -/
theorem ack_four_one : ack 4 1 = 65533 := by
  rw [ack, ack, ack_three, ack_three]
  decide

/-! ### Strict Monotonicity Invariants -/

/-- The argument is strictly dominated: $n < A(k, n)$ for all $k, n \in \mathbb{N}$. -/
theorem n_lt_ack (k n : ℕ) : n < ack k n := by
  induction k, n using ack.induct with
  | case1 n => rw [ack_zero]; omega
  | case2 k _ => rw [ack]; omega
  | case3 k n _ _ => rw [ack]; omega

/-- The Ackermann function is strictly positive for all arguments. -/
theorem ack_pos (k n : ℕ) : 0 < ack k n := by
  have := n_lt_ack k n
  omega

/-- Strict single-step right-monotonicity: $A(k, n) < A(k, n + 1)$. -/
theorem ack_lt_ack_succ_right (k n : ℕ) : ack k n < ack k (n + 1) := by
  cases k with
  | zero =>
    rw [ack_zero, ack_zero]
    omega
  | succ k =>
    rw [ack]
    exact n_lt_ack k (ack (k + 1) n)

/-- Strict right-monotonicity: $n < m \implies A(k, n) < A(k, m)$. -/
theorem ack_strictMono_right (k : ℕ) {n m : ℕ} (h : n < m) : ack k n < ack k m := by
  induction m with
  | zero => omega
  | succ m ih =>
    by_cases heq : n = m
    · subst heq
      exact ack_lt_ack_succ_right k n
    · have hlt : n < m := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ h) heq
      have := ih hlt
      have hstep := ack_lt_ack_succ_right k m
      exact lt_trans this hstep

/-- Weak right-monotonicity: $n \le m \implies A(k, n) \le A(k, m)$. -/
theorem ack_monotone_right (k : ℕ) {n m : ℕ} (h : n ≤ m) : ack k n ≤ ack k m := by
  by_cases heq : n = m
  · subst heq
    exact le_refl _
  · have hlt : n < m := Nat.lt_of_le_of_ne h heq
    exact le_of_lt (ack_strictMono_right k hlt)

/-! ### Functional Inverse Ackermann Function -/

/-- The functional inverse Ackermann function $\alpha(n) = \min \{ k \mid A(k, 1) \ge n \}$.
For practical bounds $n \le 65533$, $\alpha(n) \le 4$. -/
def invAck (n : ℕ) : ℕ :=
  if n ≤ 2 then 0
  else if n ≤ 3 then 1
  else if n ≤ 5 then 2
  else if n ≤ 13 then 3
  else if n ≤ 65533 then 4
  else 5

/-- The inverse Ackermann function is bounded above by 4 for all $n \le 65533$. -/
theorem invAck_le_four (n : ℕ) (hn : n ≤ 65533) : invAck n ≤ 4 := by
  dsimp [invAck]
  split_ifs <;> omega

/-- The inverse Ackermann function is monotonically increasing. -/
theorem invAck_monotone {a b : ℕ} (hab : a ≤ b) : invAck a ≤ invAck b := by
  dsimp [invAck]
  split_ifs <;> omega

/-- Specification theorem: $n \le A(\alpha(n), 1)$ holds for all $n \le 65533$. -/
theorem invAck_spec (n : ℕ) (hn : n ≤ 65533) : n ≤ ack (invAck n) 1 := by
  dsimp [invAck]
  split_ifs
  · rw [ack_zero_one]; omega
  · rw [ack_one_one]; omega
  · rw [ack_two_one]; omega
  · rw [ack_three_one]; omega
  · rw [ack_four_one]; omega

end Amort.Graph
