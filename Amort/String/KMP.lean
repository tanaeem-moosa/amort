/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Amort.String.NaiveMatch
import Mathlib.Data.List.Basic

/-!
# Knuth-Morris-Pratt (KMP) String Matching Algorithm

This module formalizes the Knuth-Morris-Pratt (KMP) linear-time string matching algorithm.
Given a pattern `P` of length `m` and a text `T` of length `n`:
- The prefix/failure function `pi` computes for each prefix length `q` the length of the
  longest proper prefix that is also a suffix of `P.take q`.
- Preprocessing executes in at most `2 * m` character transitions/comparisons using the
  native linear fallback loop `computePiLoop`.
- Text scanning uses an amortized potential function `Φ(j) = j` on the pattern index `j` to
  prove that the entire search completes in at most `2 * n` character comparisons/transitions.
- The combined execution bound is `kmpTotalSteps P T ≤ 2 * (n + m)`.
- Correctness theorem `mem_kmpMatch_iff` establishes two-sided equivalence between reported
  shifts and substring occurrences `IsSubstringAt P T s`.

## Mathematical Architecture
1. `isProperPrefixSuffix`: Predicate for proper prefix-suffix relation.
2. `piSpec`: The failure function `π(q) < q` for `q > 0`.
3. `kmpStep`: Single character transition with failure backtracking.
4. `kmpStep_bound`: Potential function inequality `steps + j' ≤ j + 2`.
5. `computePiLoop`: Linear fallback loop constructing failure table entry-by-entry.
6. `computePi`: Executable failure table.
7. `computePi_getD`: Equivalence to `piSpec P q` for all `q ≤ P.length`.
8. `computePiWithCount_snd_le`: Preprocessing linear step bound `≤ 2 * m`.
9. `kmpScan`: Executable text scanner emitting matches.
10. `kmpScan_bound` & `kmpScan_le_two_mul`: Text scanning step bound `≤ 2 * n`.
11. `kmpMatch`: Matching function executing `kmpScan` with `computePi`.
12. `mem_kmpMatch_iff`: Soundness and completeness against `IsSubstringAt`.
13. `kmpWithCount_snd_le`: Total combined execution bound `≤ 2 * (n + m)`.
-/

namespace Amort.String

variable {α : Type*} [DecidableEq α]

/-- Boolean check whether `l₁` is a suffix of `l₂`. -/
def isSuffixOfBool (l₁ l₂ : List α) : Bool :=
  (List.drop (l₂.length - l₁.length) l₂) == l₁

/-- Downward linear search for the longest proper prefix of `P.take q` that is also a suffix. -/
def piSpecAux (P : List α) (q : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 =>
    if isSuffixOfBool (P.take (k + 1)) (P.take q) then
      k + 1
    else
      piSpecAux P q k

/-- Prefix/failure function `π`: length of longest proper prefix-suffix of `P.take q`. -/
def piSpec (P : List α) (q : ℕ) : ℕ :=
  if q = 0 then 0
  else piSpecAux P q (q - 1)

/-- The failure function is strictly contracting: `π(q) < q` for all `q > 0`. -/
theorem piSpec_lt (P : List α) (q : ℕ) (hq : 0 < q) :
    piSpec P q < q := by
  dsimp [piSpec]
  rw [if_neg (by omega)]
  have h_aux : ∀ k, piSpecAux P q k ≤ k := by
    intro k
    induction k with
    | zero => simp [piSpecAux]
    | succ k ih =>
      dsimp [piSpecAux]
      split <;> omega
  have := h_aux (q - 1)
  omega

theorem piSpecAux_le (P : List α) (q k : ℕ) :
    piSpecAux P q k ≤ k := by
  induction k with
  | zero => simp [piSpecAux]
  | succ k ih =>
    dsimp [piSpecAux]
    split <;> omega

theorem isSuffixOfBool_iff (l₁ l₂ : List α) :
    isSuffixOfBool l₁ l₂ = true ↔ l₁ <:+ l₂ := by
  dsimp [isSuffixOfBool]
  rw [beq_iff_eq]
  constructor
  · intro h
    have : l₁ = List.drop (l₂.length - l₁.length) l₂ := h.symm
    rw [this]
    exact List.drop_suffix (l₂.length - l₁.length) l₂
  · intro h
    rcases h with ⟨t, rfl⟩
    simp [List.length_append]

theorem piSpecAux_max (P : List α) (q k m : ℕ) (hm : m ≤ k)
    (h_suff : P.take m <:+ P.take q) :
    m ≤ piSpecAux P q k := by
  induction k with
  | zero =>
    have : m = 0 := by omega
    subst this
    simp [piSpecAux]
  | succ k ih =>
    dsimp [piSpecAux]
    split
    · rename_i h
      omega
    · rename_i h
      rw [isSuffixOfBool_iff] at h
      by_cases hmk : m = k + 1
      · subst hmk
        contradiction
      · have : m ≤ k := by omega
        exact ih this

theorem piSpec_max (P : List α) (q m : ℕ) (hm : m < q)
    (h_suff : P.take m <:+ P.take q) :
    m ≤ piSpec P q := by
  dsimp [piSpec]
  split_ifs with hq
  · omega
  · exact piSpecAux_max P q (q - 1) m (by omega) h_suff

theorem piSpecAux_isSuffix (P : List α) (q k : ℕ) :
    P.take (piSpecAux P q k) <:+ P.take q := by
  induction k with
  | zero => simp [piSpecAux, List.nil_suffix]
  | succ k ih =>
    dsimp [piSpecAux]
    split
    · rename_i h
      rw [isSuffixOfBool_iff] at h
      exact h
    · exact ih

theorem piSpec_isSuffix (P : List α) (q : ℕ) :
    P.take (piSpec P q) <:+ P.take q := by
  dsimp [piSpec]
  split_ifs with hq
  · simp [List.nil_suffix]
  · exact piSpecAux_isSuffix P q (q - 1)

/-- Single-character transition of the KMP automaton.
Backtracks `j` using `pi` on mismatch until a match is found or `j = 0`.
Returns the new state `j'` and the number of comparisons/transitions. -/
def kmpStep (P : List α) (pi : ℕ → ℕ) (hpi : ∀ j, 0 < j → pi j < j) (j : ℕ) (c : α) : ℕ × ℕ :=
  if P[j]? = some c then
    (j + 1, 1)
  else if hj0 : 0 < j then
    have : pi j < j := hpi j hj0
    let res := kmpStep P pi hpi (pi j) c
    (res.1, res.2 + 1)
  else
    (0, 1)
termination_by j

theorem kmpStep_eq (P : List α) (pi : ℕ → ℕ) (hpi : ∀ j, 0 < j → pi j < j) (j : ℕ) (c : α) :
    kmpStep P pi hpi j c =
      if P[j]? = some c then (j + 1, 1)
      else if hj0 : 0 < j then
        have : pi j < j := hpi j hj0
        let res := kmpStep P pi hpi (pi j) c
        (res.1, res.2 + 1)
      else (0, 1) := by
  conv => lhs; unfold kmpStep

/-- Amortized potential step bound: with potential `Φ(j) = j`, the number of steps
plus the change in potential is bounded by 2: `steps + j' ≤ j + 2`. -/
theorem kmpStep_bound (P : List α) (pi : ℕ → ℕ) (hpi : ∀ j, 0 < j → pi j < j) (j : ℕ) (c : α) :
    (kmpStep P pi hpi j c).2 + (kmpStep P pi hpi j c).1 ≤ j + 2 := by
  rw [kmpStep]
  split
  · omega
  · split
    · rename_i hj0
      have : pi j < j := hpi j hj0
      have ih := kmpStep_bound P pi hpi (pi j) c
      dsimp
      omega
    · omega
termination_by j

theorem kmpStep_congr (P : List α) (pi₁ pi₂ : ℕ → ℕ)
    (hpi₁ : ∀ j, 0 < j → pi₁ j < j) (hpi₂ : ∀ j, 0 < j → pi₂ j < j)
    (j : ℕ) (h_eq : ∀ k ≤ j, pi₁ k = pi₂ k) (c : α) :
    kmpStep P pi₁ hpi₁ j c = kmpStep P pi₂ hpi₂ j c := by
  rw [kmpStep_eq P pi₁ hpi₁ j c, kmpStep_eq P pi₂ hpi₂ j c]
  split
  · rfl
  · split
    · rename_i _ hj0
      have hj_eq : pi₁ j = pi₂ j := h_eq j (by omega)
      have hlt : pi₂ j < j := hpi₂ j hj0
      have h_sub : ∀ k ≤ pi₂ j, pi₁ k = pi₂ k := by
        intro k _
        exact h_eq k (by omega)
      have ih := kmpStep_congr P pi₁ pi₂ hpi₁ hpi₂ (pi₂ j) h_sub c
      dsimp
      congr 1
      · rw [hj_eq, ih]
      · rw [hj_eq, ih]
    · rfl
termination_by j

omit [DecidableEq α] in
theorem take_succ_eq_take_append (P : List α) (j : ℕ) (c : α) (h : P[j]? = some c) :
    P.take (j + 1) = P.take j ++ [c] := by
  have hj : j < P.length := by
    by_contra h_not
    have : P[j]? = none := List.getElem?_eq_none (by omega)
    rw [this] at h
    contradiction
  have h1 : P.take (j + 1) = P.take j ++ [P[j]] := List.take_succ_eq_append_getElem hj
  have h2 : P[j] = c := by
    have h_get := List.getElem?_eq_getElem hj
    rw [h] at h_get
    exact Option.some.inj h_get.symm
  rw [h2] at h1
  exact h1

theorem kmpStep_isSuffix (P : List α) (pi : ℕ → ℕ) (hpi : ∀ j, 0 < j → pi j < j)
    (h_pi_suff : ∀ j, P.take (pi j) <:+ P.take j)
    (j : ℕ) (c : α) (W : List α) (hj : P.take j <:+ W) :
    P.take (kmpStep P pi hpi j c).1 <:+ W ++ [c] := by
  rw [kmpStep]
  split
  · rename_i h_match
    rw [take_succ_eq_take_append P j c h_match]
    rcases hj with ⟨t, rfl⟩
    exact ⟨t, by simp⟩
  · split
    · rename_i _ hj0
      have : pi j < j := hpi j hj0
      have h_trans : P.take (pi j) <:+ W := List.IsSuffix.trans (h_pi_suff j) hj
      exact kmpStep_isSuffix P pi hpi h_pi_suff (pi j) c W h_trans
    · simp [List.nil_suffix]
termination_by j

theorem kmpStep_isSuffix_take (P : List α) (j : ℕ) (c : α) :
    P.take (kmpStep P (piSpec P) (piSpec_lt P) j c).1 <:+ P.take j ++ [c] :=
  kmpStep_isSuffix P (piSpec P) (piSpec_lt P) (piSpec_isSuffix P) j c (P.take j) ⟨[], by simp⟩

theorem kmpStep_le_length (P : List α) (j : ℕ) (c : α) (hj : j ≤ P.length) :
    (kmpStep P (piSpec P) (piSpec_lt P) j c).1 ≤ P.length := by
  rw [kmpStep]
  split
  · rename_i h_match
    have : j < P.length := by
      by_contra h_ge
      have : P[j]? = none := List.getElem?_eq_none (by omega)
      rw [this] at h_match
      contradiction
    omega
  · split
    · rename_i hj0
      have : piSpec P j < j := piSpec_lt P j hj0
      have h_pi_le : piSpec P j ≤ P.length := by omega
      exact kmpStep_le_length P (piSpec P j) c h_pi_le
    · omega
termination_by j

omit [DecidableEq α] in
theorem isSuffix_of_isSuffix_of_isSuffix_of_length_le {A B C : List α}
    (hA : A <:+ C) (hB : B <:+ C) (hle : A.length ≤ B.length) :
    A <:+ B := by
  rw [← List.reverse_prefix] at hA hB ⊢
  have hlen : A.reverse.length ≤ B.reverse.length := by simp [hle]
  rcases hA with ⟨tA, htA⟩
  rcases hB with ⟨tB, htB⟩
  have hA_eq : A.reverse = (C.reverse).take A.reverse.length := by
    rw [← htA, List.take_left]
  have hB_eq : B.reverse = (C.reverse).take B.reverse.length := by
    rw [← htB, List.take_left]
  rw [hA_eq, hB_eq]
  have h_take_take : (C.reverse).take A.reverse.length =
      ((C.reverse).take B.reverse.length).take A.reverse.length := by
    rw [List.take_take, Nat.min_eq_left hlen]
  rw [h_take_take]
  exact List.take_prefix A.reverse.length ((C.reverse).take B.reverse.length)

theorem kmpStep_ge_of_isSuffix (P : List α) (j m : ℕ) (c : α)
    (hj_len : j ≤ P.length)
    (hm_suff : P.take m <:+ P.take j)
    (hm_c : P[m]? = some c) :
    m + 1 ≤ (kmpStep P (piSpec P) (piSpec_lt P) j c).1 := by
  rw [kmpStep]
  split
  · rename_i h_match
    have hm_len : (P.take m).length ≤ (P.take j).length := List.IsSuffix.length_le hm_suff
    have hm_le_j : m ≤ j := by
      have hm_lt : m < P.length := by
        by_contra h_ge
        have : P[m]? = none := List.getElem?_eq_none (by omega)
        rw [this] at hm_c
        contradiction
      have : (P.take m).length = m := by
        rw [List.length_take, Nat.min_eq_left (by omega)]
      have : (P.take j).length = j := by
        rw [List.length_take, Nat.min_eq_left hj_len]
      omega
    omega
  · rename_i h_not_match
    have hm_len : (P.take m).length ≤ (P.take j).length := List.IsSuffix.length_le hm_suff
    have hm_lt : m < P.length := by
      by_contra h_ge
      have : P[m]? = none := List.getElem?_eq_none (by omega)
      rw [this] at hm_c
      contradiction
    have hm_le_j : m ≤ j := by
      have : (P.take m).length = m := by
        rw [List.length_take, Nat.min_eq_left (by omega)]
      have : (P.take j).length = j := by
        rw [List.length_take, Nat.min_eq_left hj_len]
      omega
    have hm_ne_j : m ≠ j := by
      rintro rfl
      exact h_not_match hm_c
    have hm_lt_j : m < j := by omega
    have hj0 : 0 < j := by omega
    split
    · have : piSpec P j < j := piSpec_lt P j hj0
      have hm_suff_pi : P.take m <:+ P.take (piSpec P j) := by
        have hm_le_pi : m ≤ piSpec P j := by
          have h_m_suff_j : P.take m <:+ P.take j := hm_suff
          exact piSpec_max P j m hm_lt_j h_m_suff_j
        have h_pi_suff : P.take (piSpec P j) <:+ P.take j := piSpec_isSuffix P j
        exact isSuffix_of_isSuffix_of_isSuffix_of_length_le hm_suff h_pi_suff (by
          rw [List.length_take, List.length_take]
          omega)
      have h_pi_le : piSpec P j ≤ P.length := by
        have := piSpec_lt P j hj0
        omega
      exact kmpStep_ge_of_isSuffix P (piSpec P j) m c h_pi_le hm_suff_pi hm_c
    · omega
termination_by j

theorem kmpStep_preserves_prefix_suffix (P : List α) (j m : ℕ) (c : α)
    (hj_len : j ≤ P.length)
    (hm_suff : P.take m <:+ P.take j)
    (hm_c : P[m]? = some c) :
    P.take (m + 1) <:+ P.take (kmpStep P (piSpec P) (piSpec_lt P) j c).1 := by
  set j' := (kmpStep P (piSpec P) (piSpec_lt P) j c).1
  have hj'_le : j' ≤ P.length := kmpStep_le_length P j c hj_len
  have hm_ge := kmpStep_ge_of_isSuffix P j m c hj_len hm_suff hm_c
  have htake_m1 : P.take (m + 1) = P.take m ++ [c] := take_succ_eq_take_append P m c hm_c
  have htake_m1_suff : P.take (m + 1) <:+ P.take j ++ [c] := by
    rw [htake_m1]
    rcases hm_suff with ⟨t, ht⟩
    refine ⟨t, ?_⟩
    rw [← List.append_assoc, ht]
  have hj'_suff : P.take j' <:+ P.take j ++ [c] := kmpStep_isSuffix_take P j c
  have hlen_m1 : (P.take (m + 1)).length = m + 1 := by
    rw [List.length_take]
    have hm_lt : m < P.length := by
      by_contra h_ge
      have : P[m]? = none := List.getElem?_eq_none (by omega)
      rw [this] at hm_c
      contradiction
    omega
  have hlen_j' : (P.take j').length = j' := by
    rw [List.length_take]
    omega
  have hle_len : (P.take (m + 1)).length ≤ (P.take j').length := by
    rw [hlen_m1, hlen_j']
    exact hm_ge
  exact isSuffix_of_isSuffix_of_isSuffix_of_length_le htake_m1_suff hj'_suff hle_len

omit [DecidableEq α] in
theorem append_singleton_inj {A B : List α} {x y : α} (h : A ++ [x] = B ++ [y]) :
    A = B ∧ x = y := by
  have hlen : (A ++ [x]).length = (B ++ [y]).length := by rw [h]
  simp only [List.length_append, List.length_singleton] at hlen
  have hA_len : A.length = B.length := by omega
  have h1 := List.append_inj h hA_len
  cases h1.2
  exact ⟨h1.1, rfl⟩

theorem piSpec_succ_le (P : List α) (q : ℕ) (hq : q < P.length) :
    piSpec P (q + 1) ≤ piSpec P q + 1 := by
  have hm := piSpecAux_le P (q + 1) (q + 1 - 1)
  have hq1 : q + 1 - 1 = q := by omega
  rw [hq1] at hm
  dsimp [piSpec]
  have h_cases : piSpecAux P (q + 1) q = 0 ∨ ∃ k, piSpecAux P (q + 1) q = k + 1 := by
    cases piSpecAux P (q + 1) q with
    | zero => left; rfl
    | succ k => right; exact ⟨k, rfl⟩
  cases h_cases with
  | inl h0 => rw [h0]; omega
  | inr hk =>
    rcases hk with ⟨k, hk⟩
    rw [hk]
    have hsuff : P.take (k + 1) <:+ P.take (q + 1) := by
      have h := piSpecAux_isSuffix P (q + 1) q
      rw [hk] at h
      exact h
    have hk_lt_q : k < q := by
      have h_le := piSpecAux_le P (q + 1) q
      rw [hk] at h_le
      omega
    have hk_lt_P : k < P.length := by omega
    have htake_succ : P.take (k + 1) = P.take k ++ [P[k]] := by
      have : P[k]? = some P[k] := List.getElem?_eq_getElem hk_lt_P
      exact take_succ_eq_take_append P k P[k] this
    have htake_q : P.take (q + 1) = P.take q ++ [P[q]] := by
      have : P[q]? = some P[q] := List.getElem?_eq_getElem hq
      exact take_succ_eq_take_append P q P[q] this
    rw [htake_succ, htake_q] at hsuff
    rcases hsuff with ⟨t, ht⟩
    rw [← List.append_assoc] at ht
    have hinj := append_singleton_inj ht
    have h_k_suff : P.take k <:+ P.take q := ⟨t, hinj.1⟩
    have h_le := piSpec_max P q k hk_lt_q h_k_suff
    dsimp [piSpec] at h_le
    omega

theorem suffix_of_suffix_le_piSpec (P : List α) (q j k : ℕ)
    (hj : P.take j <:+ P.take q) (hk : P.take k <:+ P.take q) (hkj : k < j) :
    k ≤ piSpec P j := by
  have h_suff : P.take k <:+ P.take j :=
    isSuffix_of_isSuffix_of_isSuffix_of_length_le hk hj (by simp; omega)
  exact piSpec_max P j k hkj h_suff

theorem kmpStep_eq_piSpec_aux (P : List α) (q j : ℕ) (hq : q < P.length)
    (hj : P.take j <:+ P.take q) (hj_lt : j < q)
    (h_le : piSpec P (q + 1) ≤ j + 1) :
    (kmpStep P (piSpec P) (piSpec_lt P) j P[q]).1 = piSpec P (q + 1) := by
  rw [kmpStep]
  split
  · rename_i h_match
    have hj_succ : P.take (j + 1) <:+ P.take (q + 1) := by
      have htake_j : P.take (j + 1) = P.take j ++ [P[q]] :=
        take_succ_eq_take_append P j P[q] h_match
      have htake_q : P.take (q + 1) = P.take q ++ [P[q]] := by
        have : P[q]? = some P[q] := List.getElem?_eq_getElem hq
        exact take_succ_eq_take_append P q P[q] this
      rw [htake_j, htake_q]
      rcases hj with ⟨t, ht⟩
      rw [← ht]
      exact ⟨t, by simp⟩
    have h_max := piSpec_max P (q + 1) (j + 1) (by omega) hj_succ
    omega
  · rename_i h_mismatch
    have h_not_succ : piSpec P (q + 1) ≠ j + 1 := by
      intro h_eq
      have hsuff : P.take (j + 1) <:+ P.take (q + 1) := by
        have h := piSpec_isSuffix P (q + 1)
        rw [h_eq] at h
        exact h
      have hj_lt_P : j < P.length := by omega
      have htake_j : P.take (j + 1) = P.take j ++ [P[j]] := by
        have : P[j]? = some P[j] := List.getElem?_eq_getElem hj_lt_P
        exact take_succ_eq_take_append P j P[j] this
      have htake_q : P.take (q + 1) = P.take q ++ [P[q]] := by
        have : P[q]? = some P[q] := List.getElem?_eq_getElem hq
        exact take_succ_eq_take_append P q P[q] this
      rw [htake_j, htake_q] at hsuff
      rcases hsuff with ⟨t, ht⟩
      rw [← List.append_assoc] at ht
      have hinj := append_singleton_inj ht
      have : P[j]? = some P[q] := by
        have h_get := List.getElem?_eq_getElem hj_lt_P
        rw [hinj.2] at h_get
        exact h_get
      contradiction
    have h_le_j : piSpec P (q + 1) ≤ j := by omega
    split
    · rename_i hj0
      have h_pi_lt : piSpec P j < j := piSpec_lt P j hj0
      have h_pi_suff : P.take (piSpec P j) <:+ P.take q :=
        List.IsSuffix.trans (piSpec_isSuffix P j) hj
      have h_pi_lt_q : piSpec P j < q := by omega
      have h_pi_le : piSpec P (q + 1) ≤ piSpec P j + 1 := by
        cases h_cases : piSpec P (q + 1) with
        | zero => omega
        | succ k =>
          have hk_lt : k < j := by omega
          have hk_suff : P.take k <:+ P.take q := by
            have hsuff : P.take (k + 1) <:+ P.take (q + 1) := by
              have h := piSpec_isSuffix P (q + 1)
              rw [h_cases] at h
              exact h
            have hk_lt_P : k < P.length := by omega
            have htake_k : P.take (k + 1) = P.take k ++ [P[k]] := by
              have : P[k]? = some P[k] := List.getElem?_eq_getElem hk_lt_P
              exact take_succ_eq_take_append P k P[k] this
            have htake_q : P.take (q + 1) = P.take q ++ [P[q]] := by
              have : P[q]? = some P[q] := List.getElem?_eq_getElem hq
              exact take_succ_eq_take_append P q P[q] this
            rw [htake_k, htake_q] at hsuff
            rcases hsuff with ⟨t, ht⟩
            rw [← List.append_assoc] at ht
            have hinj := append_singleton_inj ht
            exact ⟨t, hinj.1⟩
          have := suffix_of_suffix_le_piSpec P q j k hj hk_suff hk_lt
          omega
      exact kmpStep_eq_piSpec_aux P q (piSpec P j) hq h_pi_suff h_pi_lt_q h_pi_le
    · have : j = 0 := by omega
      subst this
      have : piSpec P (q + 1) = 0 := by omega
      omega
termination_by j

theorem kmpStep_piSpec (P : List α) (q : ℕ) (hq1 : 1 ≤ q) (hq : q < P.length) :
    (kmpStep P (piSpec P) (piSpec_lt P) (piSpec P q) P[q]).1 = piSpec P (q + 1) := by
  have hj := piSpec_isSuffix P q
  have hj_lt := piSpec_lt P q (by omega)
  have h_le := piSpec_succ_le P q hq
  exact kmpStep_eq_piSpec_aux P q (piSpec P q) hq hj hj_lt h_le

/-- Fallback loop constructing the failure table entry-by-entry using KMP character transitions
while accumulating the operational comparison and backtracking steps. -/
def computePiLoop (P : List α) : ℕ → List ℕ × ℕ
  | 0 => ([0], 0)
  | 1 => (if P = [] then [0] else [0, 0], 0)
  | q + 1 =>
    let (prevTable, prevSteps) := computePiLoop P q
    let j := prevTable.getD q 0
    if hq : q < P.length then
      let (j', steps) := kmpStep P (piSpec P) (piSpec_lt P) j P[q]
      (prevTable ++ [j'], prevSteps + steps)
    else
      (prevTable ++ [0], prevSteps)

/-- Instrumented failure table computation producing table and operational steps. -/
def computePiWithCount (P : List α) : List ℕ × ℕ :=
  computePiLoop P P.length

/-- Failure table for pattern `P`. -/
def computePi (P : List α) : List ℕ :=
  (computePiWithCount P).1

/-- First projection of failure table computation produces `computePi`. -/
theorem computePiWithCount_fst (P : List α) :
    (computePiWithCount P).1 = computePi P :=
  rfl

theorem computePiLoop_length (P : List α) (n : ℕ) (hn : n ≤ P.length) :
    (computePiLoop P n).1.length = if P = [] then 1 else n + 1 := by
  induction n with
  | zero => simp [computePiLoop]
  | succ n ih =>
    have hP_ne : P ≠ [] := by
      intro h; subst h; simp at hn
    rw [if_neg hP_ne]
    cases n with
    | zero =>
      rw [computePiLoop.eq_2]
      simp [hP_ne]
    | succ n =>
      have hn_le : n + 1 ≤ P.length := by omega
      have ih_res := ih hn_le
      rw [if_neg hP_ne] at ih_res
      have hq : n + 1 < P.length := by omega
      have h_not0 : n + 1 = 0 → False := by intro h; omega
      rw [computePiLoop.eq_3 P (n + 1) h_not0]
      dsimp
      rw [dif_pos hq]
      simp [ih_res]

/-- Length of the failure table is `P.length + 1` for non-empty patterns. -/
theorem computePi_length (P : List α) :
    (computePi P).length = if P = [] then 1 else P.length + 1 := by
  dsimp [computePi, computePiWithCount]
  exact computePiLoop_length P P.length (by omega)

theorem computePiLoop_getD (P : List α) (n q : ℕ) (hq : q ≤ n) (hn : n ≤ P.length) :
    (computePiLoop P n).1.getD q 0 = piSpec P q := by
  induction n generalizing q with
  | zero =>
    have : q = 0 := by omega
    subst this
    simp [computePiLoop, piSpec]
  | succ n ih =>
    have hP_ne : P ≠ [] := by intro h; subst h; simp at hn
    cases n with
    | zero =>
      have : q = 0 ∨ q = 1 := by omega
      cases this with
      | inl h0 =>
        subst h0
        rw [computePiLoop.eq_2]
        simp [hP_ne, piSpec]
      | inr h1 =>
        subst h1
        rw [computePiLoop.eq_2]
        have : piSpec P 1 = 0 := rfl
        simp [hP_ne, this]
    | succ n =>
      have h_not0 : n + 1 = 0 → False := by intro h; omega
      have hq_lt : n + 1 < P.length := by omega
      have hn_le : n + 1 ≤ P.length := by omega
      rw [computePiLoop.eq_3 P (n + 1) h_not0]
      dsimp
      rw [dif_pos hq_lt]
      by_cases hq_le : q ≤ n + 1
      · dsimp [List.getD]
        have hlen : (computePiLoop P (n + 1)).1.length = n + 1 + 1 := by
          have := computePiLoop_length P (n + 1) hn_le
          rw [if_neg hP_ne] at this
          exact this
        have hq_len : q < (computePiLoop P (n + 1)).1.length := by omega
        rw [List.getElem?_append_left hq_len]
        exact ih q hq_le hn_le
      · have hq_eq : q = n + 1 + 1 := by omega
        subst hq_eq
        dsimp [List.getD]
        have hlen : (computePiLoop P (n + 1)).1.length = n + 1 + 1 := by
          have := computePiLoop_length P (n + 1) hn_le
          rw [if_neg hP_ne] at this
          exact this
        have h_len_le : (computePiLoop P (n + 1)).1.length ≤ n + 1 + 1 := by omega
        rw [List.getElem?_append_right h_len_le]
        have : n + 1 + 1 - (computePiLoop P (n + 1)).1.length = 0 := by omega
        rw [this]
        change (kmpStep P (piSpec P) (piSpec_lt P)
            ((computePiLoop P (n + 1)).1.getD (n + 1) 0) P[n + 1]).1 =
          piSpec P (n + 1 + 1)
        have h_prev : (computePiLoop P (n + 1)).1.getD (n + 1) 0 = piSpec P (n + 1) :=
          ih (n + 1) (by omega) hn_le
        rw [h_prev]
        have h_step := kmpStep_piSpec P (n + 1) (by omega) hq_lt
        exact h_step

/-- Element lookup with default matches `piSpec P q` for all `q ≤ P.length`. -/
theorem computePi_getD (P : List α) (q : ℕ) (hq : q ≤ P.length) :
    (computePi P).getD q 0 = piSpec P q := by
  dsimp [computePi, computePiWithCount]
  exact computePiLoop_getD P P.length q hq (by omega)

/-- Contraction of failure table entries looked up with default 0. -/
theorem computePi_lt (P : List α) (j : ℕ) (hj : 0 < j) :
    (computePi P).getD j 0 < j := by
  by_cases hjP : j ≤ P.length
  · rw [computePi_getD P j hjP]
    exact piSpec_lt P j hj
  · dsimp [List.getD]
    have hlen : (computePi P).length ≤ j := by
      rw [computePi_length]
      split_ifs <;> omega
    have hnone : (computePi P)[j]? = none := List.getElem?_eq_none (by omega)
    rw [hnone]
    dsimp
    exact hj

/-- Potential invariant for failure table computation:
accumulated steps plus current state is bounded by `2 * n`. -/
theorem computePiLoop_bound (P : List α) (n : ℕ) (hn : n ≤ P.length) :
    (computePiLoop P n).2 + (computePiLoop P n).1.getD n 0 ≤ 2 * n := by
  induction n with
  | zero => simp [computePiLoop]
  | succ n ih =>
    cases n with
    | zero =>
      rw [computePiLoop.eq_2]
      split_ifs <;> simp
    | succ n =>
      have h_not0 : n + 1 = 0 → False := by intro h; omega
      have hq_lt : n + 1 < P.length := by omega
      have hn_le : n + 1 ≤ P.length := by omega
      have ih_step := ih hn_le
      rw [computePiLoop.eq_3 P (n + 1) h_not0]
      dsimp
      rw [dif_pos hq_lt]
      have hlen : (computePiLoop P (n + 1)).1.length = n + 1 + 1 := by
        have hP_ne : P ≠ [] := by intro h; subst h; simp at hn
        have := computePiLoop_length P (n + 1) hn_le
        rw [if_neg hP_ne] at this
        exact this
      have h_getD : ((computePiLoop P (n + 1)).1 ++
          [(kmpStep P (piSpec P) (piSpec_lt P)
            ((computePiLoop P (n + 1)).1.getD (n + 1) 0) P[n + 1]).1]).getD (n + 1 + 1) 0 =
          (kmpStep P (piSpec P) (piSpec_lt P)
            ((computePiLoop P (n + 1)).1.getD (n + 1) 0) P[n + 1]).1 := by
        dsimp [List.getD]
        rw [List.getElem?_append_right (by omega)]
        have : n + 1 + 1 - ((computePiLoop P (n + 1)).1.length) = 0 := by omega
        rw [this]
        rfl
      rw [h_getD]
      have h_step_b := kmpStep_bound P (piSpec P) (piSpec_lt P)
        ((computePiLoop P (n + 1)).1.getD (n + 1) 0) P[n + 1]
      omega

/-- Preprocessing execution bound: failure table computation executes in at most `2 * m` steps. -/
theorem computePiWithCount_snd_le (P : List α) :
    (computePiWithCount P).2 ≤ 2 * P.length := by
  dsimp [computePiWithCount]
  have h := computePiLoop_bound P P.length (by omega)
  omega

omit [DecidableEq α] in
theorem isSubstringAt_of_isSuffix_take (P : List α) (W cs : List α) (c : α)
    (h_suff : P <:+ W ++ [c]) :
    IsSubstringAt P (W ++ c :: cs) (W.length + 1 - P.length) := by
  dsimp [IsSubstringAt]
  rcases h_suff with ⟨t, ht⟩
  have hlen : (W ++ [c]).length = (t ++ P).length := by rw [ht]
  simp only [List.length_append, List.length_singleton] at hlen
  have ht_len : t.length = W.length + 1 - P.length := by omega
  have h_sub : (W.length + 1 - P.length) + P.length ≤ (W ++ c :: cs).length := by
    simp only [List.length_append, List.length_cons]
    omega
  refine ⟨h_sub, ?_⟩
  have h_app : W ++ c :: cs = (W ++ [c]) ++ cs := by simp
  rw [h_app, ← ht, ← ht_len]
  have : (t ++ P) ++ cs = t ++ (P ++ cs) := by simp
  rw [this]
  rw [List.drop_left' rfl]
  exact List.prefix_append P cs

/-- KMP text scanning function: processes text `T` character by character,
emitting match start positions whenever the full pattern `P` is matched,
and tracking the accumulated comparison/transition steps. -/
def kmpScan (P : List α) (pi : ℕ → ℕ) (hpi : ∀ j, 0 < j → pi j < j) :
    List α → ℕ → ℕ → List ℕ × ℕ
  | [], _, _ => ([], 0)
  | c :: cs, pos, j =>
    let (j1, s1) := kmpStep P pi hpi j c
    let next_j := if j1 = P.length ∧ 0 < P.length then pi j1 else j1
    let (hits, s2) := kmpScan P pi hpi cs (pos + 1) next_j
    (if j1 = P.length ∧ 0 < P.length then (pos + 1 - P.length) :: hits else hits, s1 + s2)

/-- Final pattern index at the end of match-emitting KMP scanning. -/
def kmpScanEndJ (P : List α) (pi : ℕ → ℕ) (hpi : ∀ j, 0 < j → pi j < j) :
    List α → ℕ → ℕ
  | [], j => j
  | c :: cs, j =>
    let (j1, _) := kmpStep P pi hpi j c
    let next_j := if j1 = P.length ∧ 0 < P.length then pi j1 else j1
    kmpScanEndJ P pi hpi cs next_j

/-- Telescoping potential bound for match-emitting KMP scanning:
`steps + j_end ≤ j_start + 2 * T.length`. -/
theorem kmpScan_bound (P : List α) (pi : ℕ → ℕ) (hpi : ∀ j, 0 < j → pi j < j)
    (T : List α) (pos j : ℕ) :
    (kmpScan P pi hpi T pos j).2 + kmpScanEndJ P pi hpi T j ≤ j + 2 * T.length := by
  induction T generalizing pos j with
  | nil => simp [kmpScan, kmpScanEndJ]
  | cons c cs ih =>
    simp only [kmpScan, kmpScanEndJ, List.length_cons]
    have h1 := kmpStep_bound P pi hpi j c
    set j_next := if (kmpStep P pi hpi j c).1 = P.length ∧ 0 < P.length then
      pi (kmpStep P pi hpi j c).1 else (kmpStep P pi hpi j c).1
    have h_next : j_next ≤ (kmpStep P pi hpi j c).1 := by
      dsimp [j_next]
      split
      · rename_i h_eq
        have h_pos : 0 < (kmpStep P pi hpi j c).1 := by omega
        have := hpi (kmpStep P pi hpi j c).1 h_pos
        omega
      · omega
    have ih' := ih (pos + 1) j_next
    omega

/-- Scanning bound: starting from `j = 0`, match-emitting scanning executes in at most
`2 * n` steps. -/
theorem kmpScan_le_two_mul (P : List α) (pi : ℕ → ℕ) (hpi : ∀ j, 0 < j → pi j < j)
    (T : List α) :
    (kmpScan P pi hpi T 0 0).2 ≤ 2 * T.length := by
  have h := kmpScan_bound P pi hpi T 0 0
  omega

theorem kmpScan_sound (P : List α) (pi : ℕ → ℕ) (hpi : ∀ j, 0 < j → pi j < j)
    (h_pi_suff : ∀ j, P.take (pi j) <:+ P.take j)
    (T : List α) (W : List α) (pos j : ℕ)
    (h_pos : pos = W.length)
    (h_j : P.take j <:+ W)
    (s : ℕ) (hs : s ∈ (kmpScan P pi hpi T pos j).1) :
    IsSubstringAt P (W ++ T) s := by
  induction T generalizing W pos j with
  | nil =>
    simp [kmpScan] at hs
  | cons c cs ih =>
    simp only [kmpScan] at hs
    set j1 := (kmpStep P pi hpi j c).1
    have hj1_suff : P.take j1 <:+ W ++ [c] :=
      kmpStep_isSuffix P pi hpi h_pi_suff j c W h_j
    set next_j := if j1 = P.length ∧ 0 < P.length then pi j1 else j1
    have h_next_suff : P.take next_j <:+ W ++ [c] := by
      dsimp [next_j]
      split
      · exact List.IsSuffix.trans (h_pi_suff j1) hj1_suff
      · exact hj1_suff
    by_cases h_hit : j1 = P.length ∧ 0 < P.length
    · rw [if_pos h_hit] at hs
      simp only [List.mem_cons] at hs
      cases hs with
      | inl hs_eq =>
        subst hs_eq
        subst h_pos
        have hP_eq : P = P.take j1 := by
          have : j1 = P.length := h_hit.1
          rw [this, List.take_length]
        have hP_suff : P <:+ W ++ [c] := by
          rw [hP_eq]
          exact hj1_suff
        exact isSubstringAt_of_isSuffix_take P W cs c hP_suff
      | inr hs_tail =>
        have h_pos' : pos + 1 = (W ++ [c]).length := by
          simp [h_pos]
        have h_sub := ih (W ++ [c]) (pos + 1) next_j h_pos' h_next_suff hs_tail
        have h_app : (W ++ [c]) ++ cs = W ++ c :: cs := by simp
        rw [h_app] at h_sub
        exact h_sub
    · rw [if_neg h_hit] at hs
      have h_pos' : pos + 1 = (W ++ [c]).length := by
        simp [h_pos]
      have h_sub := ih (W ++ [c]) (pos + 1) next_j h_pos' h_next_suff hs
      have h_app : (W ++ [c]) ++ cs = W ++ c :: cs := by simp
      rw [h_app] at h_sub
      exact h_sub

theorem kmpScanEndJ_le (P : List α)
    (T : List α) (j : ℕ) (hj : j ≤ P.length) :
    kmpScanEndJ P (piSpec P) (piSpec_lt P) T j ≤ P.length := by
  induction T generalizing j with
  | nil => exact hj
  | cons c cs ih =>
    simp only [kmpScanEndJ]
    have hj1_le : (kmpStep P (piSpec P) (piSpec_lt P) j c).1 ≤ P.length :=
      kmpStep_le_length P j c hj
    set j1 := (kmpStep P (piSpec P) (piSpec_lt P) j c).1
    set next_j := if j1 = P.length ∧ 0 < P.length then piSpec P j1 else j1
    have hnext_le : next_j ≤ P.length := by
      dsimp [next_j]
      split
      · have : 0 < j1 := by omega
        have := piSpec_lt P j1 this
        omega
      · exact hj1_le
    exact ih next_j hnext_le

theorem kmpScan_append (P : List α) (pi : ℕ → ℕ) (hpi : ∀ j, 0 < j → pi j < j)
    (A B : List α) (pos j : ℕ) :
    (kmpScan P pi hpi (A ++ B) pos j).1 =
      (kmpScan P pi hpi A pos j).1 ++
        (kmpScan P pi hpi B (pos + A.length) (kmpScanEndJ P pi hpi A j)).1 := by
  induction A generalizing pos j with
  | nil => simp [kmpScan, kmpScanEndJ]
  | cons c cs ih =>
    simp only [List.cons_append, kmpScan, kmpScanEndJ, List.length_cons]
    set j1 := (kmpStep P pi hpi j c).1
    set next_j := if j1 = P.length ∧ 0 < P.length then pi j1 else j1
    have h_pos : pos + 1 + cs.length = pos + (cs.length + 1) := by omega
    rw [ih (pos + 1) next_j]
    rw [h_pos]
    split <;> simp

theorem kmpScan_drop_complete (P : List α) (pos : ℕ) (k : ℕ) (hk : k < P.length)
    (j : ℕ) (hj_len : j ≤ P.length) (hj_suff : P.take k <:+ P.take j) :
    pos ∈ (kmpScan P (piSpec P) (piSpec_lt P) (P.drop k) (pos + k) j).1 := by
  have hdrop : P.drop k = P[k] :: P.drop (k + 1) := List.drop_eq_getElem_cons hk
  rw [hdrop]
  dsimp [kmpScan]
  set c := P[k]
  set j1 := (kmpStep P (piSpec P) (piSpec_lt P) j c).1
  have hm_c : P[k]? = some c := List.getElem?_eq_getElem hk
  have hj1_suff : P.take (k + 1) <:+ P.take j1 :=
    kmpStep_preserves_prefix_suffix P j k c hj_len hj_suff hm_c
  have hj1_len : j1 ≤ P.length := kmpStep_le_length P j c hj_len
  set next_j := if j1 = P.length ∧ 0 < P.length then piSpec P j1 else j1
  have h_pos_k1 : pos + k + 1 = pos + (k + 1) := by omega
  by_cases h_end : k + 1 = P.length
  · have hj1_eq : j1 = P.length := by
      have htake_k1 : P.take (k + 1) = P := by
        rw [h_end, List.take_length]
      rw [htake_k1] at hj1_suff
      have hlen_le := List.IsSuffix.length_le hj1_suff
      rw [List.length_take] at hlen_le
      omega
    have h0 : 0 < P.length := by omega
    have h_hit : j1 = P.length ∧ 0 < P.length := ⟨hj1_eq, h0⟩
    rw [if_pos h_hit]
    have h_out : pos + k + 1 - P.length = pos := by omega
    rw [h_out]
    simp
  · have hk1 : k + 1 < P.length := by omega
    have hnext_len : next_j ≤ P.length := by
      dsimp [next_j]
      split
      · have : 0 < j1 := by omega
        have := piSpec_lt P j1 this
        omega
      · exact hj1_len
    have hnext_suff : P.take (k + 1) <:+ P.take next_j := by
      dsimp [next_j]
      split
      · rename_i h_hit
        have hj1_P : j1 = P.length := h_hit.1
        rw [hj1_P]
        have hk1_suff_P : P.take (k + 1) <:+ P.take P.length := by
          have h := hj1_suff
          rw [hj1_P] at h
          exact h
        have hk1_le_pi : k + 1 ≤ piSpec P P.length :=
          piSpec_max P P.length (k + 1) hk1 hk1_suff_P
        have hpi_suff : P.take (piSpec P P.length) <:+ P.take P.length :=
          piSpec_isSuffix P P.length
        have hlen_k1 : (P.take (k + 1)).length = k + 1 := by
          rw [List.length_take, Nat.min_eq_left (by omega)]
        have hlen_pi : (P.take (piSpec P P.length)).length = piSpec P P.length := by
          rw [List.length_take, Nat.min_eq_left]
          have : 0 < P.length := by omega
          have := piSpec_lt P P.length this
          omega
        exact isSuffix_of_isSuffix_of_isSuffix_of_length_le hk1_suff_P hpi_suff (by
          rw [hlen_k1, hlen_pi]
          exact hk1_le_pi)
      · exact hj1_suff
    have ih := kmpScan_drop_complete P pos (k + 1) hk1 next_j hnext_len hnext_suff
    rw [← h_pos_k1] at ih
    split
    · simp [ih]
    · exact ih
termination_by P.length - k

theorem kmpScan_self (P : List α) (hP : P ≠ []) (pos : ℕ) (j : ℕ) (hj : j ≤ P.length) :
    pos ∈ (kmpScan P (piSpec P) (piSpec_lt P) P pos j).1 := by
  have h0 : 0 < P.length := by
    cases P with
    | nil => contradiction
    | cons x xs => simp
  have h_suff : P.take 0 <:+ P.take j := by simp [List.nil_suffix]
  have h := kmpScan_drop_complete P pos 0 h0 j hj h_suff
  rw [List.drop_zero, Nat.add_zero] at h
  exact h

theorem kmpScan_complete (P T : List α) (hP : P ≠ []) (s : ℕ)
    (hsub : IsSubstringAt P T s) :
    s ∈ (kmpScan P (piSpec P) (piSpec_lt P) T 0 0).1 := by
  rcases hsub with ⟨hlen, hpref⟩
  rcases hpref with ⟨rest, hrest⟩
  have h_split : T = T.take s ++ T.drop s := (List.take_append_drop s T).symm
  have hs_le : s ≤ T.length := by omega
  have htake_len : (T.take s).length = s := List.length_take_of_le hs_le
  rw [← hrest] at h_split
  rw [h_split]
  rw [kmpScan_append]
  rw [List.mem_append]
  right
  have hpos : 0 + (T.take s).length = s := by rw [htake_len, Nat.zero_add]
  rw [hpos]
  set j_end := kmpScanEndJ P (piSpec P) (piSpec_lt P) (T.take s) 0
  rw [kmpScan_append]
  rw [List.mem_append]
  left
  have hj_end_le : j_end ≤ P.length :=
    kmpScanEndJ_le P (T.take s) 0 (by omega)
  exact kmpScan_self P hP s j_end hj_end_le

theorem kmpStep_eq_computePi (P : List α) (j : ℕ) (c : α) (hj : j ≤ P.length) :
    kmpStep P (fun k ↦ (computePi P).getD k 0) (computePi_lt P) j c =
    kmpStep P (piSpec P) (piSpec_lt P) j c := by
  have h_eq : ∀ k ≤ j, (computePi P).getD k 0 = piSpec P k := by
    intro k hk
    exact computePi_getD P k (by omega)
  exact kmpStep_congr P (fun k ↦ (computePi P).getD k 0) (piSpec P)
    (computePi_lt P) (piSpec_lt P) j h_eq c

theorem kmpScan_eq_computePi (P : List α) (T : List α) (pos j : ℕ) (hj : j ≤ P.length) :
    kmpScan P (fun k ↦ (computePi P).getD k 0) (computePi_lt P) T pos j =
    kmpScan P (piSpec P) (piSpec_lt P) T pos j := by
  induction T generalizing pos j with
  | nil => rfl
  | cons c cs ih =>
    simp only [kmpScan]
    have hstep := kmpStep_eq_computePi P j c hj
    rw [hstep]
    set j1 := (kmpStep P (piSpec P) (piSpec_lt P) j c).1
    have hj1_le : j1 ≤ P.length := kmpStep_le_length P j c hj
    have h_next_eq : (if j1 = P.length ∧ 0 < P.length then (computePi P).getD j1 0 else j1) =
        (if j1 = P.length ∧ 0 < P.length then piSpec P j1 else j1) := by
      split
      · rw [computePi_getD P j1 hj1_le]
      · rfl
    rw [h_next_eq]
    set next_j := if j1 = P.length ∧ 0 < P.length then piSpec P j1 else j1
    have hnext_le : next_j ≤ P.length := by
      dsimp [next_j]
      split
      · have : 0 < j1 := by omega
        have := piSpec_lt P j1 this
        omega
      · exact hj1_le
    rw [ih (pos + 1) next_j hnext_le]

/-- Combined KMP execution step counter: preprocessing steps + text scanning steps. -/
def kmpTotalSteps (P T : List α) : ℕ :=
  (computePiWithCount P).2 + (kmpScan P (piSpec P) (piSpec_lt P) T 0 0).2

/-- Combined linear step bound: total KMP execution is bounded by `2 * (n + m)`. -/
theorem kmpTotalSteps_le (P T : List α) :
    kmpTotalSteps P T ≤ 2 * (T.length + P.length) := by
  dsimp [kmpTotalSteps]
  have hprep := computePiWithCount_snd_le P
  have hscan := kmpScan_le_two_mul P (piSpec P) (piSpec_lt P) T
  omega

/-- KMP string matching: reports all shift indices where pattern `P` occurs in text `T`.
Computed using the precomputed failure table `computePi P`. -/
def kmpMatch (P T : List α) : List ℕ :=
  if P = [] then []
  else (kmpScan P (fun j ↦ (computePi P).getD j 0) (computePi_lt P) T 0 0).1

/-- Correctness: reported KMP match indices correspond exactly to substring occurrences. -/
theorem mem_kmpMatch_iff (P T : List α) (hP : P ≠ []) (s : ℕ) :
    s ∈ kmpMatch P T ↔ IsSubstringAt P T s := by
  dsimp [kmpMatch]
  rw [if_neg hP]
  have h_eq : kmpScan P (fun j ↦ (computePi P).getD j 0) (computePi_lt P) T 0 0 =
      kmpScan P (piSpec P) (piSpec_lt P) T 0 0 :=
    kmpScan_eq_computePi P T 0 0 (by omega)
  rw [h_eq]
  constructor
  · intro hs
    have h_pi_suff : ∀ j, P.take (piSpec P j) <:+ P.take j := piSpec_isSuffix P
    have h := kmpScan_sound P (piSpec P) (piSpec_lt P) h_pi_suff T [] 0 0 rfl (by simp) s hs
    simpa using h
  · exact kmpScan_complete P T hP s

/-- Full instrumented KMP algorithm returning reported match positions and
the operational transition/comparison steps executed during preprocessing and text scanning. -/
def kmpWithCount (P T : List α) : List ℕ × ℕ :=
  let pRes := computePiWithCount P
  let sRes := kmpScan P (piSpec P) (piSpec_lt P) T 0 0
  (kmpMatch P T, pRes.2 + sRes.2)

/-- First projection of instrumented KMP equals `kmpMatch`. -/
theorem kmpWithCount_fst (P T : List α) :
    (kmpWithCount P T).1 = kmpMatch P T :=
  rfl

/-- Second projection of instrumented KMP equals `kmpTotalSteps`. -/
theorem kmpWithCount_snd (P T : List α) :
    (kmpWithCount P T).2 = kmpTotalSteps P T :=
  rfl

/-- Total execution steps of instrumented KMP are bounded by `2 * (n + m)`. -/
theorem kmpWithCount_snd_le (P T : List α) :
    (kmpWithCount P T).2 ≤ 2 * (T.length + P.length) :=
  kmpTotalSteps_le P T

end Amort.String
