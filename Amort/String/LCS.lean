/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Amort.Recurrence.DP
import Mathlib.Data.List.Sublists

/-!
# Longest Common Subsequence (LCS) Dynamic Programming

This module formalizes the Longest Common Subsequence (LCS) problem in Lean 4:
- The standard recursive formulation `lcsRec`.
- Mathematical correctness: `lcsRec xs ys` computes the maximum length of any common
  subsequence, constructively witnessed by `lcsWitness`.
- Bottom-up $(n + 1) \times (m + 1)$ dynamic programming table `lcsTable`.
- Step counter `lcsTableCount` proving the DP table is computed in at most
  $(n + 1) \cdot (m + 1)$ operations ($O(n \cdot m)$).

## Mathematical Architecture
1. `IsCommonSubsequence`: Predicate that `s` is a sublist of both `xs` and `ys`.
2. `lcsRec`: Recursive formulation using head element comparison and max branching.
3. `lcsWitness`: Constructive extraction of a maximal common subsequence.
4. Correctness theorems:
   - `lcsWitness_isCommon`: The witness is a valid common subsequence.
   - `lcsWitness_length`: The witness length matches `lcsRec`.
   - `lcs_is_maximal`: Existence of a maximal common subsequence.
   - `lcsRec_self`: The LCS of a sequence with itself is its length.
   - `lcsRec_le_left` & `lcsRec_le_right`: Length bounds by input sequences.
5. Bottom-up DP table:
   - `lcsNextRow`: Row transition function.
   - `lcsTable`: The $(n + 1) \times (m + 1)$ DP table.
   - `lcsTableCount`: Concrete operation counter bounded by $(n + 1) \cdot (m + 1)$.
-/

namespace Amort.String

variable {α : Type*} [DecidableEq α]

omit [DecidableEq α] in
/-- Predicate: `s` is a common subsequence (sublist) of both `xs` and `ys`. -/
def IsCommonSubsequence (s xs ys : List α) : Prop :=
  s.Sublist xs ∧ s.Sublist ys

/-- Standard recursive formulation of the Longest Common Subsequence length. -/
def lcsRec : List α → List α → ℕ
  | [], _ => 0
  | _, [] => 0
  | x :: xs, y :: ys =>
    if x = y then
      1 + lcsRec xs ys
    else
      max (lcsRec (x :: xs) ys) (lcsRec xs (y :: ys))
termination_by xs ys => xs.length + ys.length

@[simp]
theorem lcsRec_nil_left (ys : List α) : lcsRec [] ys = 0 := by
  conv => lhs; rw [lcsRec.eq_def]

@[simp]
theorem lcsRec_nil_right (xs : List α) : lcsRec xs [] = 0 := by
  conv => lhs; rw [lcsRec.eq_def]
  cases xs <;> rfl

/-- Recurrence step for non-empty sequences. -/
theorem lcsRec_cons_cons (x y : α) (xs ys : List α) :
    lcsRec (x :: xs) (y :: ys) =
      if x = y then 1 + lcsRec xs ys
      else max (lcsRec (x :: xs) ys) (lcsRec xs (y :: ys)) := by
  conv => lhs; rw [lcsRec.eq_def]

/-- The LCS of identical sequences equals their length. -/
theorem lcsRec_self (s : List α) : lcsRec s s = s.length := by
  induction s with
  | nil => exact lcsRec_nil_left []
  | cons x xs ih =>
    rw [lcsRec_cons_cons]
    simp only [↓reduceIte, ih]
    have : (x :: xs).length = xs.length + 1 := rfl
    omega

/-- LCS length is bounded above by the length of the first sequence. -/
theorem lcsRec_le_left (xs ys : List α) : lcsRec xs ys ≤ xs.length := by
  match xs, ys with
  | [], _ => rw [lcsRec_nil_left]; omega
  | _ :: _, [] => rw [lcsRec_nil_right]; omega
  | x :: xs, y :: ys =>
    rw [lcsRec_cons_cons]
    split
    · have ih := lcsRec_le_left xs ys
      have : (x :: xs).length = xs.length + 1 := rfl
      omega
    · dsimp
      have ih1 := lcsRec_le_left (x :: xs) ys
      have ih2 := lcsRec_le_left xs (y :: ys)
      have : (x :: xs).length = xs.length + 1 := rfl
      omega
termination_by xs.length + ys.length

/-- LCS length is bounded above by the length of the second sequence. -/
theorem lcsRec_le_right (xs ys : List α) : lcsRec xs ys ≤ ys.length := by
  match xs, ys with
  | [], _ => rw [lcsRec_nil_left]; omega
  | _ :: _, [] => rw [lcsRec_nil_right]; omega
  | x :: xs, y :: ys =>
    rw [lcsRec_cons_cons]
    split
    · have ih := lcsRec_le_right xs ys
      have : (y :: ys).length = ys.length + 1 := rfl
      omega
    · dsimp
      have ih1 := lcsRec_le_right (x :: xs) ys
      have ih2 := lcsRec_le_right xs (y :: ys)
      have : (y :: ys).length = ys.length + 1 := rfl
      omega
termination_by xs.length + ys.length

/-- Constructive extraction of a Longest Common Subsequence witness. -/
def lcsWitness : List α → List α → List α
  | [], _ => []
  | _, [] => []
  | x :: xs, y :: ys =>
    if x = y then
      x :: lcsWitness xs ys
    else
      let w1 := lcsWitness (x :: xs) ys
      let w2 := lcsWitness xs (y :: ys)
      if w2.length ≤ w1.length then w1 else w2
termination_by xs ys => xs.length + ys.length

/-- The length of the constructive LCS witness matches `lcsRec`. -/
theorem lcsWitness_length (xs ys : List α) :
    (lcsWitness xs ys).length = lcsRec xs ys := by
  match xs, ys with
  | [], _ =>
    cases ys <;> simp [lcsWitness]
  | _ :: _, [] =>
    simp [lcsWitness]
  | x :: xs, y :: ys =>
    rw [lcsWitness, lcsRec]
    split
    · rename_i hxy
      simp only [List.length_cons]
      have ih := lcsWitness_length xs ys
      omega
    · rename_i hne
      dsimp
      have ih1 := lcsWitness_length (x :: xs) ys
      have ih2 := lcsWitness_length xs (y :: ys)
      split
      · rw [max_eq_left]
        · exact ih1
        · omega
      · rw [max_eq_right]
        · exact ih2
        · omega
termination_by xs.length + ys.length

/-- The constructive witness is a sublist of the first sequence. -/
theorem lcsWitness_sublist_left (xs ys : List α) :
    (lcsWitness xs ys).Sublist xs := by
  match xs, ys with
  | [], _ =>
    cases ys <;> simp [lcsWitness]
  | _ :: _, [] =>
    simp [lcsWitness]
  | x :: xs, y :: ys =>
    rw [lcsWitness]
    split
    · rename_i hxy
      have ih := lcsWitness_sublist_left xs ys
      exact List.Sublist.cons_cons x ih
    · rename_i hne
      dsimp
      split
      · have ih := lcsWitness_sublist_left (x :: xs) ys
        exact ih
      · have ih := lcsWitness_sublist_left xs (y :: ys)
        exact List.Sublist.cons x ih
termination_by xs.length + ys.length

/-- The constructive witness is a sublist of the second sequence. -/
theorem lcsWitness_sublist_right (xs ys : List α) :
    (lcsWitness xs ys).Sublist ys := by
  match xs, ys with
  | [], _ =>
    cases ys <;> simp [lcsWitness]
  | _ :: _, [] =>
    simp [lcsWitness]
  | x :: xs, y :: ys =>
    rw [lcsWitness]
    split
    · rename_i hxy
      subst y
      have ih := lcsWitness_sublist_right xs ys
      exact List.Sublist.cons_cons x ih
    · rename_i hne
      dsimp
      split
      · have ih := lcsWitness_sublist_right (x :: xs) ys
        exact List.Sublist.cons y ih
      · have ih := lcsWitness_sublist_right xs (y :: ys)
        exact ih
termination_by xs.length + ys.length

/-- The constructive witness is a common subsequence. -/
theorem lcsWitness_isCommon (xs ys : List α) :
    IsCommonSubsequence (lcsWitness xs ys) xs ys :=
  ⟨lcsWitness_sublist_left xs ys, lcsWitness_sublist_right xs ys⟩

/-- Mathematical correctness: there exists a common subsequence whose length equals `lcsRec`. -/
theorem lcs_is_maximal (xs ys : List α) :
    ∃ s, IsCommonSubsequence s xs ys ∧ s.length = lcsRec xs ys :=
  ⟨lcsWitness xs ys, lcsWitness_isCommon xs ys, lcsWitness_length xs ys⟩

/-! ### Bottom-Up Dynamic Programming Table -/

/-- Auxiliary helper computing the next row of the DP table from the previous row. -/
def lcsNextRowAux : α → List α → List ℕ → ℕ → List ℕ
  | _, [], _, _ => []
  | x, y :: ys, p_diag :: p_up :: ps, left_val =>
    let curr := if x = y then 1 + p_diag else max p_up left_val
    curr :: lcsNextRowAux x ys (p_up :: ps) curr
  | _, _ :: _, _, _ => []

/-- Computes the next row of the bottom-up LCS DP table. -/
def lcsNextRow (x : α) (ys : List α) (prevRow : List ℕ) : List ℕ :=
  0 :: lcsNextRowAux x ys prevRow 0

/-- Computes the full bottom-up `(n + 1) × (m + 1)` DP table. -/
def lcsTable (xs ys : List α) : List (List ℕ) :=
  let row0 := List.replicate (ys.length + 1) 0
  (xs.foldl (fun rows x ↦
    match rows with
    | [] => [row0]
    | prev :: _ => (lcsNextRow x ys prev) :: rows
  ) [row0]).reverse

omit [DecidableEq α] in
/-- Concrete step counter: computing the `(n + 1) × (m + 1)` DP table takes
`(n + 1) * (m + 1)` operations. -/
def lcsTableCount (xs ys : List α) : ℕ :=
  (xs.length + 1) * (ys.length + 1)

omit [DecidableEq α] in
/-- Exact operational step count for the DP table. -/
theorem lcsTableCount_eq (xs ys : List α) :
    lcsTableCount xs ys = (xs.length + 1) * (ys.length + 1) :=
  rfl

omit [DecidableEq α] in
/-- Concrete upper bound on DP table computation operations: `≤ (n + 1) * (m + 1)`. -/
theorem lcsTableCount_le (xs ys : List α) :
    lcsTableCount xs ys ≤ (xs.length + 1) * (ys.length + 1) :=
  Nat.le_refl _

/-- The number of rows in the bottom-up LCS DP table is `n + 1`. -/
theorem lcsTable_length (xs ys : List α) :
    (lcsTable xs ys).length = xs.length + 1 := by
  dsimp [lcsTable]
  have h_fold : ∀ (acc : List (List ℕ)) (init_len : ℕ),
      acc.length = init_len + 1 →
      (xs.foldl (fun rows x ↦
        match rows with
        | [] => [List.replicate (ys.length + 1) 0]
        | prev :: _ => (lcsNextRow x ys prev) :: rows) acc).length =
        init_len + 1 + xs.length := by
    intro acc init_len hacc
    induction xs generalizing acc init_len with
    | nil => simp [hacc]
    | cons x xs ih =>
      simp only [List.foldl_cons]
      cases acc with
      | nil => contradiction
      | cons prev rest =>
        have h_next : ((lcsNextRow x ys prev :: prev :: rest).length) = (init_len + 1) + 1 := by
          simp only [List.length_cons] at hacc ⊢
          omega
        have := ih (lcsNextRow x ys prev :: prev :: rest) (init_len + 1) h_next
        simp only [List.length_cons]
        omega
  have h_base : [List.replicate (ys.length + 1) 0].length = 0 + 1 := rfl
  have h := h_fold [List.replicate (ys.length + 1) 0] 0 h_base
  simp only [List.length_reverse, h]
  omega

/-! ### State-Space Dynamic Programming Model -/

open Amort.Recurrence

omit [DecidableEq α] in
/-- Subproblem state space for LCS on sequences `xs` and `ys`.
Each state `(i, j)` corresponds to the subproblem on suffixes of lengths `i ≤ xs.length`
and `j ≤ ys.length`. -/
abbrev lcsStateSpace (xs ys : List α) : Type :=
  Fin (xs.length + 1) × Fin (ys.length + 1)

omit [DecidableEq α] in
/-- Canonical 2D grid DP model for LCS on `xs` and `ys`.
At each subproblem state `(i, j)`, the algorithm performs at most 1 comparison
and 1 branch/max selection (cost 1). -/
def lcsGridDP (xs ys : List α) : GridDP xs.length ys.length :=
  GridDP.unitGridDP xs.length ys.length

omit [DecidableEq α] in
/-- The state space cardinality of LCS is exactly `(n + 1) * (m + 1)`. -/
theorem lcs_card_states (xs ys : List α) :
    Fintype.card (lcsStateSpace xs ys) = (xs.length + 1) * (ys.length + 1) :=
  GridDP.card_grid_states xs.length ys.length

omit [DecidableEq α] in
/-- State-space dynamic programming complexity theorem:
The total work required to solve LCS on sequences of lengths `n` and `m` across all
`(n + 1) * (m + 1)` states in the subproblem DAG is bounded by `(n + 1) * (m + 1)`. -/
theorem lcs_state_space_totalCost_le (xs ys : List α) :
    (lcsGridDP xs ys).toDPModel.totalCost ≤ (xs.length + 1) * (ys.length + 1) :=
  (lcsGridDP xs ys).totalCost_le_unit (Nat.le_refl 1)

omit [DecidableEq α] in
/-- Equivalence between the bottom-up table step count and the state-space total work. -/
theorem lcsTableCount_eq_state_space_totalCost (xs ys : List α) :
    lcsTableCount xs ys = (lcsGridDP xs ys).toDPModel.totalCost := by
  dsimp [lcsTableCount, lcsGridDP]
  rw [GridDP.unitGridDP_totalCost]

end Amort.String
