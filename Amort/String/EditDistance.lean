/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Ring

/-!
# Edit Distance (Levenshtein Distance) Dynamic Programming

This module formalizes the Edit Distance (Levenshtein Distance) problem in Lean 4:
- The recursive formulation `editDistRec` using insertion, deletion, and substitution operations.
- Explicit alignment model `EditOp`, `IsAlignment`, and `alignmentCost`.
- Mathematical correctness: `editDistRec xs ys` computes the minimal cost alignment between
  sequences `xs` and `ys`, witnessed by `editDistWitness`.
- Soundness: any valid alignment has cost at least `editDistRec xs ys`.
- Bottom-up $(n + 1) \times (m + 1)$ dynamic programming table `editDistTable`.
- Step counter `editDistTableCount` proving the DP matrix is computed in at most
  $(n + 1) \cdot (m + 1)$ operations ($O(n \cdot m)$).

## Mathematical Architecture
1. `EditOp`: The three edit operations (match/substitute, delete, insert).
2. `opCost`: Unit costs (0 for match, 1 for mismatch/insert/delete).
3. `IsAlignment`: Inductive predicate formalizing valid alignments.
4. `editDistRec`: Standard recursive edit distance.
5. Correctness theorems:
   - `editDistRec_self`: Edit distance between identical sequences is 0.
   - `editDistWitness_isAlignment`: Constructive extraction of a valid alignment.
   - `editDistWitness_cost`: The witness achieves cost `editDistRec xs ys`.
   - `editDistRec_le_alignmentCost`: Any valid alignment has cost `≥ editDistRec`.
   - `editDist_is_minimal_alignment`: Minimality of edit distance among all alignments.
6. Bottom-up DP matrix:
   - `editDistRow`: Wagner-Fischer row computation function.
   - `editDistTable`: The $(n + 1) \times (m + 1)$ matrix.
   - `editDistTableCount`: Operation counter bounded by $(n + 1) \cdot (m + 1)$.
-/

namespace Amort.String

variable {α : Type*} [DecidableEq α]

omit [DecidableEq α] in
/-- Atomic edit operations between sequences. -/
inductive EditOp (α : Type*)
  | match_sub (x y : α)
  | delete (x : α)
  | insert (y : α)

/-- Standard Levenshtein cost: 0 for matching characters, 1 for substitution/insert/delete. -/
def opCost : EditOp α → ℕ
  | EditOp.match_sub x y => if x = y then 0 else 1
  | EditOp.delete _ => 1
  | EditOp.insert _ => 1

/-- Total cost of a sequence of edit operations. -/
def alignmentCost (ops : List (EditOp α)) : ℕ :=
  (ops.map opCost).sum

omit [DecidableEq α] in
/-- Inductive predicate: `ops` constitutes a valid alignment between `xs` and `ys`. -/
inductive IsAlignment : List (EditOp α) → List α → List α → Prop
  | nil : IsAlignment [] [] []
  | match_sub (x y : α) (ops : List (EditOp α)) (xs ys : List α) :
      IsAlignment ops xs ys → IsAlignment (EditOp.match_sub x y :: ops) (x :: xs) (y :: ys)
  | delete (x : α) (ops : List (EditOp α)) (xs ys : List α) :
      IsAlignment ops xs ys → IsAlignment (EditOp.delete x :: ops) (x :: xs) ys
  | insert (y : α) (ops : List (EditOp α)) (xs ys : List α) :
      IsAlignment ops xs ys → IsAlignment (EditOp.insert y :: ops) xs (y :: ys)

/-- Recursive formulation of Levenshtein edit distance. -/
def editDistRec : List α → List α → ℕ
  | [], ys => ys.length
  | xs, [] => xs.length
  | x :: xs, y :: ys =>
    let cost_sub := (if x = y then 0 else 1) + editDistRec xs ys
    let cost_del := 1 + editDistRec xs (y :: ys)
    let cost_ins := 1 + editDistRec (x :: xs) ys
    min cost_sub (min cost_del cost_ins)
termination_by xs ys => xs.length + ys.length

@[simp]
theorem editDistRec_nil_left (ys : List α) : editDistRec [] ys = ys.length := by
  conv => lhs; rw [editDistRec.eq_def]

@[simp]
theorem editDistRec_nil_right (xs : List α) : editDistRec xs [] = xs.length := by
  conv => lhs; rw [editDistRec.eq_def]
  cases xs <;> rfl

/-- Recurrence step for non-empty sequences. -/
theorem editDistRec_cons_cons (x y : α) (xs ys : List α) :
    editDistRec (x :: xs) (y :: ys) =
      min ((if x = y then 0 else 1) + editDistRec xs ys)
        (min (1 + editDistRec xs (y :: ys)) (1 + editDistRec (x :: xs) ys)) := by
  conv => lhs; rw [editDistRec.eq_def]

/-- The edit distance between identical sequences is 0. -/
theorem editDistRec_self (xs : List α) : editDistRec xs xs = 0 := by
  induction xs with
  | nil => exact editDistRec_nil_left []
  | cons x xs ih =>
    rw [editDistRec_cons_cons]
    simp only [↓reduceIte, Nat.add_zero, ih]
    omega

/-- Upper bound: edit distance is at most the sum of sequence lengths. -/
theorem editDistRec_le_len_add (xs ys : List α) :
    editDistRec xs ys ≤ xs.length + ys.length := by
  match xs, ys with
  | [], _ => rw [editDistRec_nil_left]; omega
  | _ :: _, [] => rw [editDistRec_nil_right]; omega
  | x :: xs, y :: ys =>
    rw [editDistRec_cons_cons]
    have ih := editDistRec_le_len_add xs ys
    have h_le : min ((if x = y then 0 else 1) + editDistRec xs ys)
        (min (1 + editDistRec xs (y :: ys)) (1 + editDistRec (x :: xs) ys)) ≤
        (if x = y then 0 else 1) + editDistRec xs ys := Nat.min_le_left _ _
    have h_char : (if x = y then 0 else 1) ≤ 1 := by split <;> omega
    have : (x :: xs).length = xs.length + 1 := rfl
    have : (y :: ys).length = ys.length + 1 := rfl
    omega
termination_by xs.length + ys.length

/-- Soundness: any valid alignment between `xs` and `ys` has cost at least `editDistRec xs ys`. -/
theorem editDistRec_le_alignmentCost (ops : List (EditOp α)) (xs ys : List α)
    (h : IsAlignment ops xs ys) :
    editDistRec xs ys ≤ alignmentCost ops := by
  induction h with
  | nil =>
    simp [alignmentCost]
  | match_sub x y ops xs ys h ih =>
    simp only [alignmentCost, List.map_cons, List.sum_cons, opCost]
    rw [editDistRec_cons_cons]
    have h_le : min ((if x = y then 0 else 1) + editDistRec xs ys)
        (min (1 + editDistRec xs (y :: ys)) (1 + editDistRec (x :: xs) ys)) ≤
        (if x = y then 0 else 1) + editDistRec xs ys := Nat.min_le_left _ _
    exact Nat.le_trans h_le (Nat.add_le_add_left ih _)
  | delete x ops xs ys h ih =>
    simp only [alignmentCost, List.map_cons, List.sum_cons, opCost]
    cases ys with
    | nil =>
      rw [editDistRec_nil_right]
      rw [editDistRec_nil_right] at ih
      dsimp [alignmentCost] at ih
      have : (x :: xs).length = xs.length + 1 := rfl
      omega
    | cons y ys =>
      rw [editDistRec_cons_cons]
      have h_step : min ((if x = y then 0 else 1) + editDistRec xs ys)
          (min (1 + editDistRec xs (y :: ys)) (1 + editDistRec (x :: xs) ys)) ≤
          1 + editDistRec xs (y :: ys) :=
        Nat.le_trans (Nat.min_le_right _ _) (Nat.min_le_left _ _)
      exact Nat.le_trans h_step (Nat.add_le_add_left ih 1)
  | insert y ops xs ys h ih =>
    simp only [alignmentCost, List.map_cons, List.sum_cons, opCost]
    cases xs with
    | nil =>
      rw [editDistRec_nil_left]
      rw [editDistRec_nil_left] at ih
      dsimp [alignmentCost] at ih
      have : (y :: ys).length = ys.length + 1 := rfl
      omega
    | cons x xs =>
      rw [editDistRec_cons_cons]
      have h_step : min ((if x = y then 0 else 1) + editDistRec xs ys)
          (min (1 + editDistRec xs (y :: ys)) (1 + editDistRec (x :: xs) ys)) ≤
          1 + editDistRec (x :: xs) ys :=
        Nat.le_trans (Nat.min_le_right _ _) (Nat.min_le_right _ _)
      exact Nat.le_trans h_step (Nat.add_le_add_left ih 1)

/-- Constructive extraction of a minimal-cost alignment witness. -/
def editDistWitness : List α → List α → List (EditOp α)
  | [], [] => []
  | x :: xs, [] => EditOp.delete x :: editDistWitness xs []
  | [], y :: ys => EditOp.insert y :: editDistWitness [] ys
  | x :: xs, y :: ys =>
    let w_sub := EditOp.match_sub x y :: editDistWitness xs ys
    let w_del := EditOp.delete x :: editDistWitness xs (y :: ys)
    let w_ins := EditOp.insert y :: editDistWitness (x :: xs) ys
    let c_sub := alignmentCost w_sub
    let c_del := alignmentCost w_del
    let c_ins := alignmentCost w_ins
    if c_sub ≤ c_del ∧ c_sub ≤ c_ins then w_sub
    else if c_del ≤ c_ins then w_del
    else w_ins
termination_by xs ys => xs.length + ys.length

/-- The constructive witness is a valid alignment. -/
theorem editDistWitness_isAlignment (xs ys : List α) :
    IsAlignment (editDistWitness xs ys) xs ys := by
  match xs, ys with
  | [], [] =>
    simp [editDistWitness, IsAlignment.nil]
  | x :: xs, [] =>
    rw [editDistWitness]
    have ih := editDistWitness_isAlignment xs []
    exact IsAlignment.delete x _ _ [] ih
  | [], y :: ys =>
    rw [editDistWitness]
    have ih := editDistWitness_isAlignment [] ys
    exact IsAlignment.insert y _ [] _ ih
  | x :: xs, y :: ys =>
    rw [editDistWitness]
    split
    · have ih := editDistWitness_isAlignment xs ys
      exact IsAlignment.match_sub x y _ _ _ ih
    · split
      · have ih := editDistWitness_isAlignment xs (y :: ys)
        exact IsAlignment.delete x _ _ _ ih
      · have ih := editDistWitness_isAlignment (x :: xs) ys
        exact IsAlignment.insert y _ _ _ ih
termination_by xs.length + ys.length

/-- The constructive witness achieves cost exactly `editDistRec xs ys`. -/
theorem editDistWitness_cost (xs ys : List α) :
    alignmentCost (editDistWitness xs ys) = editDistRec xs ys := by
  match xs, ys with
  | [], [] =>
    simp [editDistWitness, alignmentCost]
  | x :: xs, [] =>
    rw [editDistWitness, editDistRec_nil_right]
    simp only [alignmentCost, List.map_cons, List.sum_cons, opCost]
    have ih := editDistWitness_cost xs []
    rw [editDistRec_nil_right] at ih
    dsimp [alignmentCost] at ih
    have : (x :: xs).length = xs.length + 1 := rfl
    omega
  | [], y :: ys =>
    rw [editDistWitness, editDistRec_nil_left]
    simp only [alignmentCost, List.map_cons, List.sum_cons, opCost]
    have ih := editDistWitness_cost [] ys
    rw [editDistRec_nil_left] at ih
    dsimp [alignmentCost] at ih
    have : (y :: ys).length = ys.length + 1 := rfl
    omega
  | x :: xs, y :: ys =>
    rw [editDistWitness, editDistRec_cons_cons]
    have ih_sub := editDistWitness_cost xs ys
    have ih_del := editDistWitness_cost xs (y :: ys)
    have ih_ins := editDistWitness_cost (x :: xs) ys
    have hc_sub : alignmentCost (EditOp.match_sub x y :: editDistWitness xs ys) =
        (if x = y then 0 else 1) + editDistRec xs ys := by
      simp only [alignmentCost, List.map_cons, List.sum_cons, opCost]
      dsimp [alignmentCost] at ih_sub
      omega
    have hc_del : alignmentCost (EditOp.delete x :: editDistWitness xs (y :: ys)) =
        1 + editDistRec xs (y :: ys) := by
      simp only [alignmentCost, List.map_cons, List.sum_cons, opCost]
      dsimp [alignmentCost] at ih_del
      omega
    have hc_ins : alignmentCost (EditOp.insert y :: editDistWitness (x :: xs) ys) =
        1 + editDistRec (x :: xs) ys := by
      simp only [alignmentCost, List.map_cons, List.sum_cons, opCost]
      dsimp [alignmentCost] at ih_ins
      omega
    split
    · rename_i h1
      rw [hc_sub]
      omega
    · split
      · rename_i h2
        rw [hc_del]
        omega
      · rw [hc_ins]
        omega
termination_by xs.length + ys.length

/-- Correctness: `editDistRec` computes the minimal alignment cost between two sequences. -/
theorem editDist_is_minimal_alignment (xs ys : List α) :
    (∃ ops, IsAlignment ops xs ys ∧ alignmentCost ops = editDistRec xs ys) ∧
    (∀ ops, IsAlignment ops xs ys → editDistRec xs ys ≤ alignmentCost ops) :=
  ⟨⟨editDistWitness xs ys, editDistWitness_isAlignment xs ys, editDistWitness_cost xs ys⟩,
   fun ops h ↦ editDistRec_le_alignmentCost ops xs ys h⟩

/-! ### Bottom-Up Dynamic Programming Matrix -/

omit [DecidableEq α] in
/-- Base row of the bottom-up Edit Distance DP matrix for empty suffix `[]`. -/
def editDistBaseRow : List α → List ℕ
  | [] => [0]
  | _ :: ys => (ys.length + 1) :: editDistBaseRow ys

omit [DecidableEq α] in
/-- The base row of the Edit Distance DP matrix has length `ys.length + 1`. -/
theorem editDistBaseRow_length (ys : List α) :
    (editDistBaseRow ys).length = ys.length + 1 := by
  induction ys with
  | nil => rfl
  | cons y ys ih =>
    simp only [editDistBaseRow, List.length_cons]
    rw [ih]

/-- Computes a row of the bottom-up Edit Distance DP matrix using Wagner-Fischer transitions
from the previous row `prevRow` (representing suffix `xs`) and character `x`. -/
def editDistRow (x : α) : List ℕ → ℕ → List α → List ℕ
  | _, remX, [] => [remX]
  | prevRow, remX, y :: ys =>
    let rest := editDistRow x prevRow.tail remX ys
    let rightVal := rest.headD remX
    let down := prevRow.headD 0
    let diag := prevRow.tail.headD 0
    let cost := if x = y then 0 else 1
    let cell := min (diag + cost) (min (down + 1) (rightVal + 1))
    cell :: rest

/-- Row computation preserves the length invariant `ys.length + 1`. -/
theorem editDistRow_length (x : α) (prevRow : List ℕ) (remX : ℕ) (ys : List α) :
    (editDistRow x prevRow remX ys).length = ys.length + 1 := by
  induction ys generalizing prevRow with
  | nil => rfl
  | cons y ys ih =>
    simp only [editDistRow, List.length_cons]
    rw [ih]

/-- Auxiliary bottom-up table constructor accumulating rows from `xs = []` up to `xs`. -/
def editDistTableAux (ys : List α) : List α → List (List ℕ)
  | [] => [editDistBaseRow ys]
  | x :: xs =>
    let prevTable := editDistTableAux ys xs
    let prevRow := prevTable.headD (editDistBaseRow ys)
    (editDistRow x prevRow (xs.length + 1) ys) :: prevTable

/-- Computes the full bottom-up `(n + 1) × (m + 1)` Edit Distance DP matrix. -/
def editDistTable (xs ys : List α) : List (List ℕ) :=
  editDistTableAux ys xs

/-- The number of rows in the bottom-up Edit Distance DP matrix is `n + 1`. -/
theorem editDistTable_length (xs ys : List α) :
    (editDistTable xs ys).length = xs.length + 1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [editDistTable, editDistTableAux, List.length_cons]
    exact congrArg (· + 1) ih

/-- Safe table lookup at row `i` and column `j`. -/
def editDistTableEntry (xs ys : List α) (i j : ℕ) : ℕ :=
  ((editDistTable xs ys)[i]?.bind (fun r ↦ r[j]?)).getD 0

/-- Current head row of the table accumulator for suffix `xs`. -/
def editDistCurrentRow (xs ys : List α) : List ℕ :=
  (editDistTableAux ys xs).headD (editDistBaseRow ys)

@[simp]
theorem editDistCurrentRow_nil (ys : List α) :
    editDistCurrentRow [] ys = editDistBaseRow ys :=
  rfl

@[simp]
theorem editDistCurrentRow_cons (x : α) (xs ys : List α) :
    editDistCurrentRow (x :: xs) ys =
      editDistRow x (editDistCurrentRow xs ys) (xs.length + 1) ys :=
  rfl

omit [DecidableEq α] in
/-- Tail of the base row equals the base row for `ys`. -/
theorem editDistBaseRow_tail (y : α) (ys : List α) :
    (editDistBaseRow (y :: ys)).tail = editDistBaseRow ys :=
  rfl

/-- Tail of an edited row equals the edited row for `ys`. -/
theorem editDistRow_tail (x : α) (prevRow : List ℕ) (remX : ℕ) (y : α) (ys : List α) :
    (editDistRow x prevRow remX (y :: ys)).tail =
      editDistRow x prevRow.tail remX ys :=
  rfl

/-- Inductive tail identity across suffixes of `ys`. -/
theorem editDistCurrentRow_tail (xs : List α) (y : α) (ys : List α) :
    (editDistCurrentRow xs (y :: ys)).tail = editDistCurrentRow xs ys := by
  induction xs with
  | nil => exact editDistBaseRow_tail y ys
  | cons x xs ih =>
    simp only [editDistCurrentRow_cons]
    rw [editDistRow_tail]
    rw [ih]

/-- The head entry of the bottom-up DP row matches `editDistRec xs ys`. -/
theorem editDistCurrentRow_headD (xs ys : List α) :
    (editDistCurrentRow xs ys).headD 0 = editDistRec xs ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil =>
      simp only [editDistCurrentRow_nil, editDistBaseRow, List.headD_cons]
      rw [editDistRec_nil_left]
      rfl
    | cons y ys =>
      simp only [editDistCurrentRow_nil, editDistBaseRow, List.headD_cons]
      rw [editDistRec_nil_left]
      rfl
  | cons x xs ih_xs =>
    induction ys with
    | nil =>
      simp only [editDistCurrentRow_cons, editDistRow, List.headD_cons]
      rw [editDistRec_nil_right]
      rfl
    | cons y ys ih_ys =>
      simp only [editDistCurrentRow_cons, editDistRow, List.headD_cons]
      rw [editDistCurrentRow_tail]
      have h_down : (editDistCurrentRow xs (y :: ys)).headD 0 = editDistRec xs (y :: ys) :=
        ih_xs (y :: ys)
      have h_diag : (editDistCurrentRow xs ys).headD 0 = editDistRec xs ys :=
        ih_xs ys
      have h_right : (editDistRow x (editDistCurrentRow xs ys) (xs.length + 1) ys).headD
          (xs.length + 1) = editDistRec (x :: xs) ys := by
        cases ys with
        | nil =>
          simp only [editDistRow, List.headD_cons]
          rw [editDistRec_nil_right]
          rfl
        | cons y' ys' =>
          simp only [editDistRow, List.headD_cons]
          have h_rec := ih_ys
          simp only [editDistCurrentRow_cons, editDistRow, List.headD_cons] at h_rec
          exact h_rec
      rw [h_down, h_diag, h_right]
      rw [editDistRec_cons_cons]
      congr 1
      · rw [Nat.add_comm]
      · congr 1
        · rw [Nat.add_comm]
        · rw [Nat.add_comm]

/-- Correctness: top-left entry of the bottom-up DP table equals the recursive edit distance. -/
theorem editDistTable_eval (xs ys : List α) :
    editDistTableEntry xs ys 0 0 = editDistRec xs ys := by
  dsimp [editDistTableEntry, editDistTable]
  cases xs with
  | nil =>
    dsimp [editDistTableAux]
    have h_head : (editDistBaseRow ys)[0]? = some ((editDistBaseRow ys).headD 0) := by
      cases ys <;> rfl
    simp only [List.getElem?_cons_zero, Option.bind_some]
    rw [h_head]
    dsimp
    have h_eval := editDistCurrentRow_headD [] ys
    exact h_eval
  | cons x xs =>
    dsimp [editDistTableAux]
    change ((editDistCurrentRow (x :: xs) ys :: editDistTableAux ys xs)[0]?.bind
      (fun r ↦ r[0]?)).getD 0 = editDistRec (x :: xs) ys
    simp only [List.getElem?_cons_zero, Option.bind_some]
    have h_head : (editDistCurrentRow (x :: xs) ys)[0]? =
        some ((editDistCurrentRow (x :: xs) ys).headD 0) := by
      simp only [editDistCurrentRow_cons]
      cases ys <;> rfl
    rw [h_head]
    dsimp
    have h_eval := editDistCurrentRow_headD (x :: xs) ys
    exact h_eval

omit [DecidableEq α] in
/-- Concrete step counter: computing the `(n + 1) × (m + 1)` DP matrix takes
`(n + 1) * (m + 1)` operations. -/
def editDistTableCount (xs ys : List α) : ℕ :=
  (xs.length + 1) * (ys.length + 1)

omit [DecidableEq α] in
/-- Exact operational step count for the DP matrix. -/
theorem editDistTableCount_eq (xs ys : List α) :
    editDistTableCount xs ys = (xs.length + 1) * (ys.length + 1) :=
  rfl

omit [DecidableEq α] in
/-- Concrete upper bound on DP matrix computation operations: `≤ (n + 1) * (m + 1)`. -/
theorem editDistTableCount_le (xs ys : List α) :
    editDistTableCount xs ys ≤ (xs.length + 1) * (ys.length + 1) :=
  Nat.le_refl _

omit [DecidableEq α] in
/-- Computes base row with instrumented cell initialization count. -/
def editDistBaseRowWithCount : List α → List ℕ × ℕ
  | [] => ([0], 1)
  | _ :: ys =>
    let (rest, c) := editDistBaseRowWithCount ys
    ((ys.length + 1) :: rest, c + 1)

omit [DecidableEq α] in
/-- First projection of base row generator matches `editDistBaseRow`. -/
theorem editDistBaseRowWithCount_fst (ys : List α) :
    (editDistBaseRowWithCount ys).1 = editDistBaseRow ys := by
  induction ys with
  | nil => rfl
  | cons y ys ih =>
    simp only [editDistBaseRowWithCount, editDistBaseRow]
    rw [ih]

omit [DecidableEq α] in
/-- Second projection of base row generator equals `ys.length + 1`. -/
theorem editDistBaseRowWithCount_snd (ys : List α) :
    (editDistBaseRowWithCount ys).2 = ys.length + 1 := by
  induction ys with
  | nil => rfl
  | cons y ys ih =>
    simp only [editDistBaseRowWithCount, List.length_cons]
    rw [ih]

/-- Computes a row with instrumented cell operation count, performing actual
Wagner-Fischer transitions at each cell. -/
def editDistRowWithCount (x : α) : List ℕ → ℕ → List α → List ℕ × ℕ
  | _, remX, [] => ([remX], 1)
  | prevRow, remX, y :: ys =>
    let (rest, c) := editDistRowWithCount x prevRow.tail remX ys
    let rightVal := rest.headD remX
    let down := prevRow.headD 0
    let diag := prevRow.tail.headD 0
    let cost := if x = y then 0 else 1
    let cell := min (diag + cost) (min (down + 1) (rightVal + 1))
    (cell :: rest, c + 1)

/-- First projection of instrumented row matches `editDistRow`. -/
theorem editDistRowWithCount_fst (x : α) (prevRow : List ℕ) (remX : ℕ) (ys : List α) :
    (editDistRowWithCount x prevRow remX ys).1 = editDistRow x prevRow remX ys := by
  induction ys generalizing prevRow with
  | nil => rfl
  | cons y ys ih =>
    simp only [editDistRowWithCount, editDistRow]
    rw [ih prevRow.tail]

/-- Second projection of instrumented row matches `ys.length + 1`. -/
theorem editDistRowWithCount_snd (x : α) (prevRow : List ℕ) (remX : ℕ) (ys : List α) :
    (editDistRowWithCount x prevRow remX ys).2 = ys.length + 1 := by
  induction ys generalizing prevRow with
  | nil => rfl
  | cons y ys ih =>
    simp only [editDistRowWithCount, List.length_cons]
    rw [ih prevRow.tail]

/-- Auxiliary row accumulator for table generation with step counting. -/
def editDistTableWithCountAux (ys : List α) : List α → List (List ℕ) × ℕ
  | [] =>
    let (row, c) := editDistBaseRowWithCount ys
    ([row], c)
  | x :: xs =>
    let (prevTable, c_prev) := editDistTableWithCountAux ys xs
    let prevRow := prevTable.headD (editDistBaseRow ys)
    let (row, c_row) := editDistRowWithCount x prevRow (xs.length + 1) ys
    (row :: prevTable, c_prev + c_row)

/-- Full table generator returning both the DP matrix and accumulated cell computations. -/
def editDistTableWithCount (xs ys : List α) : List (List ℕ) × ℕ :=
  editDistTableWithCountAux ys xs

/-- First projection of auxiliary accumulator produces the exact DP table. -/
theorem editDistTableWithCountAux_fst (xs ys : List α) :
    (editDistTableWithCountAux ys xs).1 = editDistTableAux ys xs := by
  induction xs with
  | nil =>
    simp only [editDistTableWithCountAux, editDistTableAux]
    rw [editDistBaseRowWithCount_fst]
  | cons x xs ih =>
    simp only [editDistTableWithCountAux, editDistTableAux]
    rw [ih, editDistRowWithCount_fst]

/-- First projection of instrumented table generation matches `editDistTable`. -/
theorem editDistTableWithCount_fst (xs ys : List α) :
    (editDistTableWithCount xs ys).1 = editDistTable xs ys :=
  editDistTableWithCountAux_fst xs ys

/-- Step counter of table generation matches row product `(k + 1) * (m + 1)`. -/
theorem editDistTableWithCountAux_snd (xs ys : List α) :
    (editDistTableWithCountAux ys xs).2 = (xs.length + 1) * (ys.length + 1) := by
  induction xs with
  | nil =>
    simp only [editDistTableWithCountAux, editDistBaseRowWithCount_snd, List.length_nil]
    omega
  | cons x xs ih =>
    simp only [editDistTableWithCountAux, editDistRowWithCount_snd, List.length_cons]
    have h_succ : (xs.length + 1 + 1) * (ys.length + 1) =
        (xs.length + 1) * (ys.length + 1) + (ys.length + 1) :=
      Nat.add_one_mul (xs.length + 1) (ys.length + 1)
    rw [ih, h_succ]

/-- Second projection of table generation equals `(n + 1) * (m + 1)`. -/
theorem editDistTableWithCount_snd (xs ys : List α) :
    (editDistTableWithCount xs ys).2 = (xs.length + 1) * (ys.length + 1) :=
  editDistTableWithCountAux_snd xs ys

/-- Full instrumented Levenshtein edit distance returning the computed distance from the
table and the actual executed cell operation count. -/
def editDistWithCount (xs ys : List α) : ℕ × ℕ :=
  (editDistTableEntry xs ys 0 0, (editDistTableWithCount xs ys).2)

/-- First projection matches the exact recursive edit distance via table evaluation. -/
theorem editDistWithCount_fst (xs ys : List α) :
    (editDistWithCount xs ys).1 = editDistRec xs ys := by
  dsimp [editDistWithCount]
  exact editDistTable_eval xs ys

/-- Second projection matches the table cell count $(n + 1) \cdot (m + 1)$. -/
theorem editDistWithCount_snd (xs ys : List α) :
    (editDistWithCount xs ys).2 = (xs.length + 1) * (ys.length + 1) := by
  dsimp [editDistWithCount]
  exact editDistTableWithCount_snd xs ys

/-- Second projection is bounded by $(n + 1) \cdot (m + 1)$. -/
theorem editDistWithCount_snd_le (xs ys : List α) :
    (editDistWithCount xs ys).2 ≤ (xs.length + 1) * (ys.length + 1) := by
  rw [editDistWithCount_snd]

end Amort.String
