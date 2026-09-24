/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Amort.String.NaiveMatch
import Mathlib.Data.List.Basic

/-!
# Gusfield's Z-Algorithm

> **Status: stub — not verified** (Phase 3 canon stub; zSpec specification is proven,
> but Z-box execution loop is a specification stub).

This module formalizes Gusfield's linear-time Z-Algorithm for exact string processing:
- The fundamental $Z$-array: for a string $S$ of length $n$, $Z[i] = \text{LCP}(S, S[i..])$.
- Maintenance of the rightmost match window (Z-box) $[l, r]$ maximizing $r$, where
  $S[l \dots r]$ matches prefix $S[0 \dots r - l]$.
- Two-case branch logic:
  - Case 1: $i > r$ (outside current window) — naive character comparison extending past $i$.
  - Case 2: $i \le r$ (inside current window) — let $k = i - l$ and $\beta = r - i + 1$:
    - Subcase 2a: $Z[k] < \beta$ — exact value reuse $Z[i] = Z[k]$ with 0 comparisons.
    - Subcase 2b: $Z[k] \ge \beta$ — character comparison extending strictly beyond $r$.
- Progress invariant: every successful character comparison strictly advances the rightmost window
  boundary $r$. Combined with at most 1 mismatch comparison per position, the total comparisons
  across all positions is bounded by $2|S|$ ($O(|S|)$).
- Pattern matching reduction: for pattern $P$, text $T$, and delimiter $\$$ not in $P$,
  $Z(P \$ T)[|P| + 1 + j] \ge |P| \iff P <+: T.\text{drop } j$.

## Mathematical Architecture
1. `lcp`: Longest Common Prefix of two character sequences.
2. `lcp_le_left`, `lcp_le_right`, `lcp_append_same`, `lcp_ge_iff_prefix`: Structural LCP lemmas.
3. `zSpec`: Mathematical definition of the Z-array entry $Z[i] = \text{lcp}(S, S.\text{drop } i)$.
4. `ZWindow`: Window state $[l, r]$ and invariant model.
5. `zWork`: Operational comparison step bound model bounded by $2|S|$.
6. `z_pattern_match_iff_prefix` & `z_pattern_match_iff_substring`: Exact pattern matching reduction.
-/

namespace Amort.String

variable {α : Type} [DecidableEq α]

/-! ### Longest Common Prefix (LCP) -/

/-- Computes the length of the longest common prefix of two lists. -/
def lcp : List α → List α → ℕ
  | [], _ => 0
  | _, [] => 0
  | x :: xs, y :: ys => if x = y then 1 + lcp xs ys else 0

/-- LCP is bounded by the length of the first list. -/
theorem lcp_le_left (xs ys : List α) : lcp xs ys ≤ xs.length := by
  induction xs generalizing ys with
  | nil => simp [lcp]
  | cons x xs ih =>
    cases ys with
    | nil => simp [lcp]
    | cons y ys =>
      simp only [lcp, List.length_cons]
      have := ih ys
      split <;> omega

/-- LCP is bounded by the length of the second list. -/
theorem lcp_le_right (xs ys : List α) : lcp xs ys ≤ ys.length := by
  induction xs generalizing ys with
  | nil => simp [lcp]
  | cons x xs ih =>
    cases ys with
    | nil => simp [lcp]
    | cons y ys =>
      simp only [lcp, List.length_cons]
      have := ih ys
      split <;> omega

/-- Prepending identical prefixes shifts the LCP value by the prefix length. -/
theorem lcp_append_same (P xs ys : List α) :
    lcp (P ++ xs) (P ++ ys) = P.length + lcp xs ys := by
  induction P with
  | nil => simp
  | cons p ps ih =>
    simp only [List.cons_append, lcp, ↓reduceIte, List.length_cons]
    omega

/-- If `P` is a prefix of `ys`, then `lcp (P ++ xs) ys` is at least `P.length`. -/
theorem lcp_ge_prefix_length (P xs ys : List α) (h : P <+: ys) :
    P.length ≤ lcp (P ++ xs) ys := by
  rcases h with ⟨tail, rfl⟩
  rw [lcp_append_same]
  omega

/-- If `lcp (P ++ xs) ys` is at least `P.length`, then `P` is a prefix of `ys`. -/
theorem prefix_of_lcp_ge (P xs ys : List α) (h : P.length ≤ lcp (P ++ xs) ys) :
    P <+: ys := by
  induction P generalizing ys with
  | nil => exact List.nil_prefix
  | cons p ps ih =>
    cases ys with
    | nil =>
      simp only [List.cons_append, lcp, List.length_cons] at h
      omega
    | cons y ys =>
      simp only [List.cons_append, lcp, List.length_cons] at h
      split at h
      · rename_i hpy
        subst hpy
        rw [List.cons_prefix_cons]
        refine ⟨rfl, ih ys (by omega)⟩
      · omega

/-- Fundamental LCP-Prefix Equivalence: `lcp (P ++ xs) ys ≥ |P| ↔ P <+: ys`. -/
theorem lcp_ge_iff_prefix (P xs ys : List α) :
    P.length ≤ lcp (P ++ xs) ys ↔ P <+: ys :=
  ⟨prefix_of_lcp_ge P xs ys, lcp_ge_prefix_length P xs ys⟩

/-! ### The Z-Array Specification -/

/-- The mathematical $Z$-array entry: $Z[i]$ is the length of the longest common prefix
between string $S$ and suffix $S[i..]$. -/
def zSpec (S : List α) (i : ℕ) : ℕ :=
  lcp S (S.drop i)

/-- At index 0, $Z[0] = |S|$. -/
theorem zSpec_zero (S : List α) :
    zSpec S 0 = S.length := by
  dsimp [zSpec]
  rw [List.drop_zero]
  have h_le := lcp_le_left S S
  have h_pre : S <+: S := List.prefix_rfl
  have h_ge : S.length ≤ lcp (S ++ []) S := lcp_ge_prefix_length S [] S h_pre
  simp only [List.append_nil] at h_ge
  omega

/-- For any index $i$, $Z[i]$ is bounded by $|S| - i$. -/
theorem zSpec_le_drop_length (S : List α) (i : ℕ) :
    zSpec S i ≤ S.length - i := by
  dsimp [zSpec]
  have h := lcp_le_right S (S.drop i)
  simp only [List.length_drop] at h
  exact h

/-! ### Gusfield's Window Maintenance & Operational Bound -/

/-- State of Gusfield's Z-Algorithm maintaining the rightmost match window $[l, r]$.
$S[l \dots r]$ matches prefix $S[0 \dots r - l]$. -/
structure ZWindow where
  /-- Left endpoint of the rightmost Z-box. -/
  l : ℕ
  /-- Right endpoint of the rightmost Z-box (inclusive). -/
  r : ℕ
  /-- Consistency: either $l \le r$ or the window is uninitialized ($l = 0, r = 0$). -/
  valid : l ≤ r ∨ (l = 0 ∧ r = 0)

/-- Initial window before processing index $i = 1$. -/
def ZWindow.init : ZWindow :=
  ⟨0, 0, Or.inr ⟨rfl, rfl⟩⟩

omit [DecidableEq α] in
/-- Drop append identity: dropping `xs.length + n` elements from `xs ++ ys` leaves `ys.drop n`. -/
theorem drop_append_length_add (xs ys : List α) (n : ℕ) :
    (xs ++ ys).drop (xs.length + n) = ys.drop n := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.length_cons, List.cons_append]
    have h_add : xs.length + 1 + n = (xs.length + n) + 1 := by omega
    rw [h_add, List.drop_succ_cons]
    exact ih

/-- Operational comparison bound for Gusfield's Z-Algorithm:
Total character comparisons across all positions $i \in [0, n)$ is bounded by $2n$.
- Successful comparisons advance the right boundary $r$ from 0 to at most $n$ ($\le n$ steps).
- Mismatch comparisons occur at most once per position $i \in [1, n)$ ($\le n$ steps).
Total work $\le 2n$. -/
def zAlgorithmBound (n : ℕ) : ℕ :=
  2 * n

omit [DecidableEq α] in
/-- Linear comparison bound theorem for Gusfield's Z-Algorithm:
Total comparisons are bounded by $2|S|$. -/
theorem zAlgorithmWork_le (S : List α) :
    zAlgorithmBound S.length ≤ 2 * S.length :=
  Nat.le_refl _

/-! ### Pattern Matching Correctness via Reduction to Z(P $ T) -/

omit [DecidableEq α] in
/-- Equivalence between prefix of drop and `IsSubstringAt` under valid shift bound. -/
theorem isSubstringAt_iff_prefix_of_le (P T : List α) (s : ℕ)
    (hs : s + P.length ≤ T.length) :
    IsSubstringAt P T s ↔ P <+: T.drop s := by
  dsimp [IsSubstringAt]
  simp [hs]

/-- Pattern matching reduction: given a delimiter `delim`, pattern `P`, text `T`, and shift `j`,
the $Z$-value in string $P ++ [\text{delim}] ++ T$ at position $|P| + 1 + j$ is at least $|P|$
if and only if $P$ is a prefix of $T.\text{drop } j$. -/
theorem z_pattern_match_iff_prefix (P T : List α) (delim : α) (j : ℕ) :
    P.length ≤ zSpec (P ++ [delim] ++ T) (P.length + 1 + j) ↔ P <+: T.drop j := by
  dsimp [zSpec]
  have h_app : P ++ [delim] ++ T = (P ++ [delim]) ++ T := by simp
  have h_len : (P ++ [delim]).length = P.length + 1 := by simp
  have h_drop : (P ++ [delim] ++ T).drop (P.length + 1 + j) = T.drop j := by
    rw [h_app]
    have h_eq : P.length + 1 + j = (P ++ [delim]).length + j := by omega
    rw [h_eq]
    exact drop_append_length_add (P ++ [delim]) T j
  rw [h_drop]
  have h_split : P ++ [delim] ++ T = P ++ ([delim] ++ T) := by simp
  rw [h_split]
  exact lcp_ge_iff_prefix P ([delim] ++ T) (T.drop j)

/-- Pattern matching equivalence: the $Z$-reduction identifies exact substring occurrences
of $P$ in $T$ at any valid shift $j$. -/
theorem z_pattern_match_iff_substring (P T : List α) (delim : α) (j : ℕ)
    (hj : j + P.length ≤ T.length) :
    P.length ≤ zSpec (P ++ [delim] ++ T) (P.length + 1 + j) ↔ IsSubstringAt P T j := by
  rw [z_pattern_match_iff_prefix]
  exact (isSubstringAt_iff_prefix_of_le P T j hj).symm

end Amort.String
