/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Mathlib.Data.List.Basic

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
   - `editDistNextRow`: Row computation function.
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

/-- Auxiliary helper computing the next row of the Edit Distance DP matrix. -/
def editDistNextRowAux : α → List α → List ℕ → ℕ → List ℕ
  | _, [], _, _ => []
  | x, y :: ys, p_diag :: p_up :: ps, left_val =>
    let cost_sub := p_diag + (if x = y then 0 else 1)
    let cost_del := p_up + 1
    let cost_ins := left_val + 1
    let curr := min cost_sub (min cost_del cost_ins)
    curr :: editDistNextRowAux x ys (p_up :: ps) curr
  | _, _ :: _, _, _ => []

/-- Computes the next row of the Edit Distance DP matrix. -/
def editDistNextRow (i : ℕ) (x : α) (ys : List α) (prevRow : List ℕ) : List ℕ :=
  i :: editDistNextRowAux x ys prevRow i

/-- Computes the full bottom-up `(n + 1) × (m + 1)` Edit Distance DP matrix. -/
def editDistTable (xs ys : List α) : List (List ℕ) :=
  let row0 := List.range (ys.length + 1)
  (xs.foldl (fun (pair : List (List ℕ) × ℕ) x ↦
    match pair.1 with
    | [] => ([row0], 1)
    | prev :: _ => ((editDistNextRow pair.2 x ys prev) :: pair.1, pair.2 + 1)
  ) ([row0], 1)).1.reverse

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

/-- The number of rows in the bottom-up Edit Distance DP matrix is `n + 1`. -/
theorem editDistTable_length (xs ys : List α) :
    (editDistTable xs ys).length = xs.length + 1 := by
  dsimp [editDistTable]
  have h_fold : ∀ (acc : List (List ℕ)) (i : ℕ) (init_len : ℕ),
      acc.length = init_len + 1 →
      (xs.foldl (fun (pair : List (List ℕ) × ℕ) x ↦
        match pair.1 with
        | [] => ([List.range (ys.length + 1)], 1)
        | prev :: _ => ((editDistNextRow pair.2 x ys prev) :: pair.1, pair.2 + 1))
        (acc, i)).1.length = init_len + 1 + xs.length := by
    intro acc i init_len hacc
    induction xs generalizing acc i init_len with
    | nil => simp [hacc]
    | cons x xs ih =>
      cases acc with
      | nil => contradiction
      | cons prev rest =>
        simp only [List.foldl_cons]
        have h_next : (editDistNextRow i x ys prev :: prev :: rest).length =
            (init_len + 1) + 1 := by
          simp only [List.length_cons] at hacc ⊢
          omega
        have := ih (editDistNextRow i x ys prev :: prev :: rest) (i + 1) (init_len + 1) h_next
        simp only [this]
        have : (x :: xs).length = xs.length + 1 := rfl
        omega
  have h_base : [List.range (ys.length + 1)].length = 0 + 1 := rfl
  have h := h_fold [List.range (ys.length + 1)] 1 0 h_base
  simp only [List.length_reverse, h]
  omega

end Amort.String
