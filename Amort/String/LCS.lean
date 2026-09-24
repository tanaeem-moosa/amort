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

omit [DecidableEq α] in
lemma sublist_cons_inv (z x : α) (zs xs : List α) (h : (z :: zs).Sublist (x :: xs)) :
    (z :: zs).Sublist xs ∨ (z = x ∧ zs.Sublist xs) := by
  cases h with
  | cons _ h =>
    left
    exact h
  | cons_cons _ h =>
    right
    exact ⟨rfl, h⟩

/-- **Optimality of LCS**:
Every common subsequence of `xs` and `ys` has length at most `lcsRec xs ys`. -/
theorem isCommonSubsequence_length_le (s xs ys : List α) (h : IsCommonSubsequence s xs ys) :
    s.length ≤ lcsRec xs ys := by
  match xs, ys with
  | [], _ =>
    have : s = [] := List.eq_nil_of_sublist_nil h.1
    subst this
    simp
  | _ :: _, [] =>
    have : s = [] := List.eq_nil_of_sublist_nil h.2
    subst this
    simp
  | x :: xs, y :: ys =>
    cases s with
    | nil => simp
    | cons z zs =>
      rw [lcsRec_cons_cons]
      have hx := sublist_cons_inv z x zs xs h.1
      have hy := sublist_cons_inv z y zs ys h.2
      by_cases hxy : x = y
      · subst hxy
        simp only [↓reduceIte]
        rcases hx with hx1 | ⟨rfl, hx2⟩
        · rcases hy with hy1 | ⟨rfl, hy2⟩
          · have ih := isCommonSubsequence_length_le (z :: zs) xs ys ⟨hx1, hy1⟩
            omega
          · have h_sub : zs.Sublist xs := (List.sublist_cons_self z zs).trans hx1
            have ih := isCommonSubsequence_length_le zs xs ys ⟨h_sub, hy2⟩
            simp only [List.length_cons]
            omega
        · rcases hy with hy1 | ⟨_hy_eq, hy2⟩
          · have h_sub : zs.Sublist ys := (List.sublist_cons_self z zs).trans hy1
            have ih := isCommonSubsequence_length_le zs xs ys ⟨hx2, h_sub⟩
            simp only [List.length_cons]
            omega
          · have ih := isCommonSubsequence_length_le zs xs ys ⟨hx2, hy2⟩
            simp only [List.length_cons]
            omega
      · rw [if_neg hxy]
        rcases hx with hx1 | ⟨rfl, hx2⟩
        · have ih := isCommonSubsequence_length_le (z :: zs) xs (y :: ys) ⟨hx1, h.2⟩
          omega
        · rcases hy with hy1 | ⟨rfl, hy2⟩
          · have ih := isCommonSubsequence_length_le (z :: zs) (z :: xs) ys ⟨h.1, hy1⟩
            omega
          · contradiction
termination_by xs.length + ys.length

/-- **Full Optimality & Correctness Characterization of LCS**:
`lcsRec xs ys` equals the length of a constructive witness, and bounds all common subsequences. -/
theorem lcs_is_optimal (xs ys : List α) :
    (∃ s, IsCommonSubsequence s xs ys ∧ s.length = lcsRec xs ys) ∧
    (∀ s, IsCommonSubsequence s xs ys → s.length ≤ lcsRec xs ys) :=
  ⟨lcs_is_maximal xs ys, fun s h ↦ isCommonSubsequence_length_le s xs ys h⟩

/-! ### Bottom-Up Dynamic Programming Table -/

omit [DecidableEq α] in
/-- Base row of the bottom-up LCS DP table corresponding to empty sequence `xs = []`. -/
def lcsBaseRow : List α → List ℕ
  | [] => [0]
  | _ :: ys => 0 :: lcsBaseRow ys

omit [DecidableEq α] in
/-- The base row has length `ys.length + 1`. -/
theorem lcsBaseRow_length (ys : List α) :
    (lcsBaseRow ys).length = ys.length + 1 := by
  induction ys with
  | nil => rfl
  | cons y ys ih =>
    simp only [lcsBaseRow, List.length_cons]
    rw [ih]

/-- Computes a row of the bottom-up LCS DP table from the previous row `prevRow`
and character `x`. -/
def lcsRow (x : α) : List ℕ → List α → List ℕ
  | _, [] => [0]
  | prevRow, y :: ys =>
    let rest := lcsRow x prevRow.tail ys
    let rightVal := rest.headD 0
    let down := prevRow.headD 0
    let diag := prevRow.tail.headD 0
    let cell := if x = y then 1 + diag else max rightVal down
    cell :: rest

/-- Row computation preserves length invariant `ys.length + 1`. -/
theorem lcsRow_length (x : α) (prevRow : List ℕ) (ys : List α) :
    (lcsRow x prevRow ys).length = ys.length + 1 := by
  induction ys generalizing prevRow with
  | nil => rfl
  | cons y ys ih =>
    simp only [lcsRow, List.length_cons]
    rw [ih]

/-- Auxiliary bottom-up table constructor accumulating rows from `xs = []` up to `xs`. -/
def lcsTableAux (ys : List α) : List α → List (List ℕ)
  | [] => [lcsBaseRow ys]
  | x :: xs =>
    let prevTable := lcsTableAux ys xs
    let prevRow := prevTable.headD (lcsBaseRow ys)
    (lcsRow x prevRow ys) :: prevTable

/-- Computes the full bottom-up `(n + 1) × (m + 1)` LCS DP table. -/
def lcsTable (xs ys : List α) : List (List ℕ) :=
  lcsTableAux ys xs

/-- The number of rows in the bottom-up LCS DP table is `n + 1`. -/
theorem lcsTable_length (xs ys : List α) :
    (lcsTable xs ys).length = xs.length + 1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [lcsTable, lcsTableAux, List.length_cons]
    exact congrArg (· + 1) ih

/-- Safe table lookup at row `i` and column `j`. -/
def lcsTableEntry (xs ys : List α) (i j : ℕ) : ℕ :=
  ((lcsTable xs ys)[i]?.bind (fun r ↦ r[j]?)).getD 0

/-- Current head row of the table accumulator for suffix `xs`. -/
def lcsCurrentRow (xs ys : List α) : List ℕ :=
  (lcsTableAux ys xs).headD (lcsBaseRow ys)

@[simp]
theorem lcsCurrentRow_nil (ys : List α) :
    lcsCurrentRow [] ys = lcsBaseRow ys := rfl

@[simp]
theorem lcsCurrentRow_cons (x : α) (xs ys : List α) :
    lcsCurrentRow (x :: xs) ys = lcsRow x (lcsCurrentRow xs ys) ys := rfl

omit [DecidableEq α] in
/-- Tail of the base row equals the base row for `ys`. -/
theorem lcsBaseRow_tail (y : α) (ys : List α) :
    (lcsBaseRow (y :: ys)).tail = lcsBaseRow ys := rfl

/-- Tail of an LCS row equals the LCS row for `ys`. -/
theorem lcsRow_tail (x : α) (prevRow : List ℕ) (y : α) (ys : List α) :
    (lcsRow x prevRow (y :: ys)).tail = lcsRow x prevRow.tail ys := rfl

/-- Inductive tail identity across suffixes of `ys`. -/
theorem lcsCurrentRow_tail (xs : List α) (y : α) (ys : List α) :
    (lcsCurrentRow xs (y :: ys)).tail = lcsCurrentRow xs ys := by
  induction xs with
  | nil => exact lcsBaseRow_tail y ys
  | cons x xs ih =>
    simp only [lcsCurrentRow_cons]
    rw [lcsRow_tail, ih]

/-- The head entry of the bottom-up DP row matches `lcsRec xs ys`. -/
theorem lcsCurrentRow_headD (xs ys : List α) :
    (lcsCurrentRow xs ys).headD 0 = lcsRec xs ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rw [lcsRec_nil_left]; rfl
    | cons y ys => rw [lcsRec_nil_left]; rfl
  | cons x xs ih_xs =>
    induction ys with
    | nil =>
      simp only [lcsCurrentRow_cons, lcsRow, List.headD_cons, lcsRec_nil_right]
    | cons y ys ih_ys =>
      simp only [lcsCurrentRow_cons, lcsRow, List.headD_cons]
      rw [lcsCurrentRow_tail]
      have h_down : (lcsCurrentRow xs (y :: ys)).headD 0 = lcsRec xs (y :: ys) :=
        ih_xs (y :: ys)
      have h_diag : (lcsCurrentRow xs ys).headD 0 = lcsRec xs ys :=
        ih_xs ys
      have h_right : (lcsRow x (lcsCurrentRow xs ys) ys).headD 0 = lcsRec (x :: xs) ys := by
        cases ys with
        | nil =>
          simp only [lcsRow, List.headD_cons, lcsRec_nil_right]
        | cons y' ys' =>
          have h_rec := ih_ys
          simp only [lcsCurrentRow_cons, lcsRow, List.headD_cons] at h_rec
          exact h_rec
      rw [h_down, h_diag, h_right]
      rw [lcsRec_cons_cons]

/-- Correctness: top-left entry of the bottom-up DP table equals recursive LCS. -/
theorem lcsTable_eval (xs ys : List α) :
    lcsTableEntry xs ys 0 0 = lcsRec xs ys := by
  dsimp [lcsTableEntry, lcsTable]
  cases xs with
  | nil =>
    dsimp [lcsTableAux]
    have h_head : (lcsBaseRow ys)[0]? = some ((lcsBaseRow ys).headD 0) := by
      cases ys <;> rfl
    simp only [List.getElem?_cons_zero, Option.bind_some]
    rw [h_head]
    dsimp
    exact lcsCurrentRow_headD [] ys
  | cons x xs =>
    dsimp [lcsTableAux]
    change ((lcsCurrentRow (x :: xs) ys :: lcsTableAux ys xs)[0]?.bind
      (fun r ↦ r[0]?)).getD 0 = lcsRec (x :: xs) ys
    simp only [List.getElem?_cons_zero, Option.bind_some]
    have h_head : (lcsCurrentRow (x :: xs) ys)[0]? =
        some ((lcsCurrentRow (x :: xs) ys).headD 0) := by
      simp only [lcsCurrentRow_cons]
      cases ys <;> rfl
    rw [h_head]
    dsimp
    exact lcsCurrentRow_headD (x :: xs) ys

omit [DecidableEq α] in
/-- Base row with cell operation counter. -/
def lcsBaseRowWithCount (ys : List α) : List ℕ × ℕ :=
  (lcsBaseRow ys, ys.length + 1)

omit [DecidableEq α] in
/-- First projection of base row matches `lcsBaseRow`. -/
theorem lcsBaseRowWithCount_fst (ys : List α) :
    (lcsBaseRowWithCount ys).1 = lcsBaseRow ys := rfl

omit [DecidableEq α] in
/-- Second projection of base row matches `ys.length + 1`. -/
theorem lcsBaseRowWithCount_snd (ys : List α) :
    (lcsBaseRowWithCount ys).2 = ys.length + 1 := rfl

/-- Instrumented row computation executing cell transitions and counting operations. -/
def lcsRowWithCount (x : α) : List ℕ → List α → List ℕ × ℕ
  | _, [] => ([0], 1)
  | prevRow, y :: ys =>
    let (rest, c) := lcsRowWithCount x prevRow.tail ys
    let rightVal := rest.headD 0
    let down := prevRow.headD 0
    let diag := prevRow.tail.headD 0
    let cell := if x = y then 1 + diag else max rightVal down
    (cell :: rest, c + 1)

/-- First projection of instrumented row matches pure `lcsRow`. -/
theorem lcsRowWithCount_fst (x : α) (prevRow : List ℕ) (ys : List α) :
    (lcsRowWithCount x prevRow ys).1 = lcsRow x prevRow ys := by
  induction ys generalizing prevRow with
  | nil => rfl
  | cons y ys ih =>
    simp only [lcsRowWithCount, lcsRow]
    rw [ih prevRow.tail]

/-- Second projection of instrumented row matches `ys.length + 1`. -/
theorem lcsRowWithCount_snd (x : α) (prevRow : List ℕ) (ys : List α) :
    (lcsRowWithCount x prevRow ys).2 = ys.length + 1 := by
  induction ys generalizing prevRow with
  | nil => rfl
  | cons y ys ih =>
    simp only [lcsRowWithCount, List.length_cons]
    rw [ih prevRow.tail]

/-- Auxiliary row accumulator for table generation with operation counting. -/
def lcsTableWithCountAux (ys : List α) : List α → List (List ℕ) × ℕ
  | [] =>
    let (row, c) := lcsBaseRowWithCount ys
    ([row], c)
  | x :: xs =>
    let (prevTable, c_prev) := lcsTableWithCountAux ys xs
    let prevRow := prevTable.headD (lcsBaseRow ys)
    let (row, c_row) := lcsRowWithCount x prevRow ys
    (row :: prevTable, c_prev + c_row)

/-- Full table generator returning both the DP matrix and accumulated cell computations. -/
def lcsTableWithCount (xs ys : List α) : List (List ℕ) × ℕ :=
  lcsTableWithCountAux ys xs

/-- First projection of auxiliary accumulator produces the exact DP table. -/
theorem lcsTableWithCountAux_fst (xs ys : List α) :
    (lcsTableWithCountAux ys xs).1 = lcsTableAux ys xs := by
  induction xs with
  | nil =>
    simp only [lcsTableWithCountAux, lcsTableAux]
    rw [lcsBaseRowWithCount_fst]
  | cons x xs ih =>
    simp only [lcsTableWithCountAux, lcsTableAux]
    rw [ih, lcsRowWithCount_fst]

/-- First projection of instrumented table generation matches `lcsTable`. -/
theorem lcsTableWithCount_fst (xs ys : List α) :
    (lcsTableWithCount xs ys).1 = lcsTable xs ys :=
  lcsTableWithCountAux_fst xs ys

/-- Step counter of table generation matches row product `(k + 1) * (m + 1)`. -/
theorem lcsTableWithCountAux_snd (xs ys : List α) :
    (lcsTableWithCountAux ys xs).2 = (xs.length + 1) * (ys.length + 1) := by
  induction xs with
  | nil =>
    simp only [lcsTableWithCountAux, lcsBaseRowWithCount_snd, List.length_nil]
    omega
  | cons x xs ih =>
    simp only [lcsTableWithCountAux, lcsRowWithCount_snd, List.length_cons]
    have h_succ : (xs.length + 1 + 1) * (ys.length + 1) =
        (xs.length + 1) * (ys.length + 1) + (ys.length + 1) :=
      Nat.add_one_mul (xs.length + 1) (ys.length + 1)
    rw [ih, h_succ]

/-- Second projection of table generation equals `(n + 1) * (m + 1)`. -/
theorem lcsTableWithCount_snd (xs ys : List α) :
    (lcsTableWithCount xs ys).2 = (xs.length + 1) * (ys.length + 1) :=
  lcsTableWithCountAux_snd xs ys

omit [DecidableEq α] in
/-- Operation count for computing the `(n + 1) × (m + 1)` DP table. -/
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

/-! ### State-Space Dynamic Programming Model -/

open Amort.Recurrence

omit [DecidableEq α] in
/-- Subproblem state space for LCS on sequences `xs` and `ys`. -/
abbrev lcsStateSpace (xs ys : List α) : Type :=
  Fin (xs.length + 1) × Fin (ys.length + 1)

omit [DecidableEq α] in
/-- Canonical 2D grid DP model for LCS on `xs` and `ys`. -/
def lcsGridDP (xs ys : List α) : GridDP xs.length ys.length :=
  GridDP.unitGridDP xs.length ys.length

omit [DecidableEq α] in
/-- The state space cardinality of LCS is exactly `(n + 1) * (m + 1)`. -/
theorem lcs_card_states (xs ys : List α) :
    Fintype.card (lcsStateSpace xs ys) = (xs.length + 1) * (ys.length + 1) :=
  GridDP.card_grid_states xs.length ys.length

omit [DecidableEq α] in
/-- State-space dynamic programming complexity theorem. -/
theorem lcs_state_space_totalCost_le (xs ys : List α) :
    (lcsGridDP xs ys).toDPModel.totalCost ≤ (xs.length + 1) * (ys.length + 1) :=
  (lcsGridDP xs ys).totalCost_le_unit (Nat.le_refl 1)

omit [DecidableEq α] in
/-- Equivalence between the bottom-up table step count and the state-space total work. -/
theorem lcsTableCount_eq_state_space_totalCost (xs ys : List α) :
    lcsTableCount xs ys = (lcsGridDP xs ys).toDPModel.totalCost := by
  dsimp [lcsTableCount, lcsGridDP]
  rw [GridDP.unitGridDP_totalCost]

/-- Full instrumented LCS algorithm returning the optimal length from the computed DP table
and the actual executed cell operation count. -/
def lcsWithCount (xs ys : List α) : ℕ × ℕ :=
  (lcsTableEntry xs ys 0 0, (lcsTableWithCount xs ys).2)

/-- First projection matches recursive LCS via DP table evaluation. -/
theorem lcsWithCount_fst (xs ys : List α) :
    (lcsWithCount xs ys).1 = lcsRec xs ys := by
  dsimp [lcsWithCount]
  exact lcsTable_eval xs ys

/-- Second projection matches executed cell operation count `(n + 1) * (m + 1)`. -/
theorem lcsWithCount_snd (xs ys : List α) :
    (lcsWithCount xs ys).2 = (xs.length + 1) * (ys.length + 1) := by
  dsimp [lcsWithCount]
  exact lcsTableWithCount_snd xs ys

/-- Second projection is bounded by `(n + 1) * (m + 1)`. -/
theorem lcsWithCount_snd_le (xs ys : List α) :
    (lcsWithCount xs ys).2 ≤ (xs.length + 1) * (ys.length + 1) := by
  rw [lcsWithCount_snd]

end Amort.String
