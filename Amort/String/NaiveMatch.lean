/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Mathlib.Data.List.Basic

/-!
# Naive Sliding-Window String Matching

This module formalizes the naive sliding-window string matching algorithm.
Given a pattern `P` of length `m` and a text `T` of length `n`:
- For each valid shift `s ∈ [0, n - m]`, character-by-character comparison checks whether `P`
  occurs at position `s` in `T`.
- The comparison counter tracks character comparisons performed, bounded in the worst case by
  `(n - m + 1) * m ≤ n * m`.
- Correctness theorems prove that match positions correspond exactly to occurrences of `P`
  as a prefix of `T.drop s`.

## Mathematical Architecture
1. `checkPrefix`: Checks whether a pattern list matches a prefix of a text list.
2. `checkPrefixCount`: Counts the number of character comparisons until mismatch or completion.
3. `naiveMatch`: Produces the list of all shift indices `s` where `P` occurs in `T`.
4. `naiveMatchCount`: Total character comparisons across all shifts.
5. Invariant & bound lemmas:
   - `checkPrefixCount_le`: At most `m` comparisons per shift.
   - `naiveMatchCount_le_shifts`: Total comparisons bounded by `(n - m + 1) * m`.
   - `naiveMatchCount_le_mul`: Total comparisons bounded by `n * m`.
   - `mem_naiveMatch_iff`: Equivalence between reported shifts and substring occurrences.
-/

namespace Amort.String

variable {α : Type*} [DecidableEq α]

/-- Checks whether pattern `P` is a prefix of text `T`. -/
def checkPrefix : List α → List α → Bool
  | [], _ => true
  | _ :: _, [] => false
  | p :: ps, t :: ts => if p = t then checkPrefix ps ts else false

/-- Counts character comparisons when testing if `P` is a prefix of `T`. Stops on mismatch. -/
def checkPrefixCount : List α → List α → ℕ
  | [], _ => 0
  | _ :: _, [] => 0
  | p :: ps, t :: ts => if p = t then 1 + checkPrefixCount ps ts else 1

/-- Instrumented prefix check returning both the match boolean and comparison count. -/
def checkPrefixWithCount : List α → List α → Bool × ℕ
  | [], _ => (true, 0)
  | _ :: _, [] => (false, 0)
  | p :: ps, t :: ts =>
    if p = t then
      let res := checkPrefixWithCount ps ts
      (res.1, 1 + res.2)
    else
      (false, 1)

@[simp]
lemma checkPrefixWithCount_fst (P T : List α) :
    (checkPrefixWithCount P T).1 = checkPrefix P T := by
  induction P generalizing T with
  | nil => rfl
  | cons p ps ih =>
    cases T with
    | nil => rfl
    | cons t ts =>
      simp only [checkPrefixWithCount, checkPrefix]
      split <;> simp [ih]

@[simp]
lemma checkPrefixWithCount_snd (P T : List α) :
    (checkPrefixWithCount P T).2 = checkPrefixCount P T := by
  induction P generalizing T with
  | nil => rfl
  | cons p ps ih =>
    cases T with
    | nil => rfl
    | cons t ts =>
      simp only [checkPrefixWithCount, checkPrefixCount]
      split <;> simp [ih]

/-- Single prefix test executes at most `P.length` character comparisons. -/
theorem checkPrefixCount_le (P T : List α) :
    checkPrefixCount P T ≤ P.length := by
  induction P generalizing T with
  | nil => simp [checkPrefixCount]
  | cons p ps ih =>
    cases T with
    | nil => simp [checkPrefixCount]
    | cons t ts =>
      simp only [checkPrefixCount, List.length_cons]
      split
      · have := ih ts
        omega
      · omega

/-- Prefix comparison is sound and complete with respect to `List.IsPrefix` (`<+:`). -/
theorem checkPrefix_iff_prefix (P T : List α) :
    checkPrefix P T = true ↔ P <+: T := by
  induction P generalizing T with
  | nil => simp [checkPrefix, List.nil_prefix]
  | cons p ps ih =>
    cases T with
    | nil => simp [checkPrefix]
    | cons t ts =>
      simp only [checkPrefix, List.cons_prefix_cons]
      split
      · subst t
        simp [ih]
      · rename_i hne
        simp [hne]

omit [DecidableEq α] in
/-- Substring occurrence predicate: pattern `P` occurs in text `T` at shift `s`. -/
def IsSubstringAt (P T : List α) (s : ℕ) : Prop :=
  s + P.length ≤ T.length ∧ P <+: T.drop s

omit [DecidableEq α] in
/-- Substring occurrence characterized by slice equality. -/
theorem isSubstringAt_iff_take_drop (P T : List α) (s : ℕ) :
    IsSubstringAt P T s ↔ s + P.length ≤ T.length ∧ (T.drop s).take P.length = P := by
  dsimp [IsSubstringAt]
  rw [List.prefix_iff_eq_take]
  constructor
  · rintro ⟨hlen, hpref⟩
    exact ⟨hlen, hpref.symm⟩
  · rintro ⟨hlen, htake⟩
    exact ⟨hlen, htake.symm⟩

/-- Naive string matching sliding-window algorithm: checks each shift `s ∈ [0, n - m]`. -/
def naiveMatch (P T : List α) : List ℕ :=
  if P.length ≤ T.length then
    (List.range (T.length - P.length + 1)).filter (fun s ↦ checkPrefix P (T.drop s))
  else []

/-- Step counter: total character comparisons made by naive matching across all shifts. -/
def naiveMatchCount (P T : List α) : ℕ :=
  if P.length ≤ T.length then
    ((List.range (T.length - P.length + 1)).map (fun s ↦ checkPrefixCount P (T.drop s))).sum
  else 0

/-- Auxiliary: sum of a mapped list is bounded by length times uniform element bound. -/
lemma sum_map_le_const {β : Type*} (l : List β) (f : β → ℕ) (c : ℕ)
    (h : ∀ x ∈ l, f x ≤ c) :
    (l.map f).sum ≤ l.length * c := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have hx : f x ≤ c := h x (List.mem_cons_self)
    have hxs : (xs.map f).sum ≤ xs.length * c :=
      ih (fun y hy ↦ h y (List.mem_cons_of_mem x hy))
    rw [Nat.add_mul, Nat.one_mul]
    omega

/-- Concrete comparison bound: total comparisons bounded by `(n - m + 1) * m`. -/
theorem naiveMatchCount_le_shifts (P T : List α) :
    naiveMatchCount P T ≤ (T.length - P.length + 1) * P.length := by
  dsimp [naiveMatchCount]
  split
  · have hsum := sum_map_le_const (List.range (T.length - P.length + 1))
        (fun s ↦ checkPrefixCount P (T.drop s)) P.length
        (fun s _ ↦ checkPrefixCount_le P (T.drop s))
    rw [List.length_range] at hsum
    exact hsum
  · simp

/-- Quadratic comparison bound: total comparisons bounded by `n * m`. -/
theorem naiveMatchCount_le_mul (P T : List α) :
    naiveMatchCount P T ≤ T.length * P.length := by
  have h := naiveMatchCount_le_shifts P T
  by_cases hle_len : P.length ≤ T.length
  · have hle : (T.length - P.length + 1) * P.length ≤ T.length * P.length := by
      cases P with
      | nil => simp
      | cons p ps =>
        have hp : 1 ≤ (p :: ps).length := by simp
        have : T.length - (p :: ps).length + 1 ≤ T.length := by omega
        exact Nat.mul_le_mul_right _ this
    exact Nat.le_trans h hle
  · dsimp [naiveMatchCount] at h ⊢
    rw [if_neg hle_len]
    exact Nat.zero_le _

/-- Correctness: reported shifts correspond exactly to substring occurrences. -/
theorem mem_naiveMatch_iff (P T : List α) (s : ℕ) :
    s ∈ naiveMatch P T ↔ IsSubstringAt P T s := by
  dsimp [naiveMatch, IsSubstringAt]
  split
  · rename_i hle
    simp only [List.mem_filter, List.mem_range, checkPrefix_iff_prefix]
    constructor
    · rintro ⟨hs, hpref⟩
      refine ⟨by omega, hpref⟩
    · rintro ⟨hs, hpref⟩
      refine ⟨by omega, hpref⟩
  · rename_i hgt
    simp only [List.not_mem_nil, false_iff]
    intro ⟨hs, _⟩
    omega

end Amort.String
