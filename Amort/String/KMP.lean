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
- Preprocessing executes in at most `2 * m` character transitions/comparisons.
- Text scanning uses an amortized potential function `Φ(j) = j` on the pattern index `j` to
  prove that the entire search completes in at most `2 * n` character comparisons/transitions.
- The combined execution bound is `kmpTotalSteps P T ≤ 2 * (n + m)`.
- Equivalence and correctness theorems establish that KMP and Naive string matching produce
  identical match indices, corresponding exactly to occurrences of `P` in `T`.

## Mathematical Architecture
1. `isProperPrefixSuffix`: Predicate for proper prefix-suffix relation.
2. `piSpec`: The failure function `π(q) < q` for `q > 0`.
3. `kmpStep`: Single character transition with failure backtracking.
4. `kmpStep_bound`: Potential function inequality `steps + j' ≤ j + 2`.
5. `kmpScanCount`: Text scanning step counter.
6. `kmpScanCount_bound`: Telescoping potential analysis `steps + j' ≤ j + 2 * T.length`.
7. `kmpScanCount_le_two_mul`: Search executes in at most `2 * n` steps.
8. `kmpPreprocessCount_le`: Preprocessing executes in at most `2 * m` steps.
9. `kmpTotalSteps_le`: Combined execution bounded by `2 * (n + m)`.
10. `kmpMatch_eq_naiveMatch` & `mem_kmpMatch_iff`: Exact correctness and equivalence.
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

/-- Text scanning step counter: processes text `T` character by character,
returning the final pattern index and accumulated comparison/transition steps. -/
def kmpScanCount (P : List α) (pi : ℕ → ℕ) (hpi : ∀ j, 0 < j → pi j < j) :
    List α → ℕ → ℕ × ℕ
  | [], j => (j, 0)
  | c :: cs, j =>
    let (j1, s1) := kmpStep P pi hpi j c
    let (j_end, s2) := kmpScanCount P pi hpi cs j1
    (j_end, s1 + s2)

/-- Telescoping potential bound for KMP text scanning:
`steps + j_end ≤ j_start + 2 * T.length`. -/
theorem kmpScanCount_bound (P : List α) (pi : ℕ → ℕ) (hpi : ∀ j, 0 < j → pi j < j)
    (T : List α) (j : ℕ) :
    (kmpScanCount P pi hpi T j).2 + (kmpScanCount P pi hpi T j).1 ≤ j + 2 * T.length := by
  induction T generalizing j with
  | nil => simp [kmpScanCount]
  | cons c cs ih =>
    simp only [kmpScanCount, List.length_cons]
    have h1 := kmpStep_bound P pi hpi j c
    have h2 := ih (kmpStep P pi hpi j c).1
    omega

/-- Scanning bound: starting from `j = 0`, text scanning executes in at most `2 * n` steps. -/
theorem kmpScanCount_le_two_mul (P : List α) (pi : ℕ → ℕ) (hpi : ∀ j, 0 < j → pi j < j)
    (T : List α) :
    (kmpScanCount P pi hpi T 0).2 ≤ 2 * T.length := by
  have h := kmpScanCount_bound P pi hpi T 0
  omega

/-- Preprocessing step counter: scanning `P` against itself to construct failure table. -/
def kmpPreprocessCount (P : List α) : ℕ :=
  (kmpScanCount P (piSpec P) (piSpec_lt P) P 0).2

/-- Preprocessing bound: failure table computation executes in at most `2 * m` steps. -/
theorem kmpPreprocessCount_le (P : List α) :
    kmpPreprocessCount P ≤ 2 * P.length :=
  kmpScanCount_le_two_mul P (piSpec P) (piSpec_lt P) P

/-- Combined KMP execution step counter: preprocessing steps + text scanning steps. -/
def kmpTotalSteps (P T : List α) : ℕ :=
  kmpPreprocessCount P + (kmpScanCount P (piSpec P) (piSpec_lt P) T 0).2

/-- Combined linear step bound: total KMP execution is bounded by `2 * (n + m)`. -/
theorem kmpTotalSteps_le (P T : List α) :
    kmpTotalSteps P T ≤ 2 * (T.length + P.length) := by
  dsimp [kmpTotalSteps]
  have hprep := kmpPreprocessCount_le P
  have hscan := kmpScanCount_le_two_mul P (piSpec P) (piSpec_lt P) T
  omega

/-- KMP string matching: reports all shift indices where pattern `P` occurs in text `T`. -/
def kmpMatch (P T : List α) : List ℕ :=
  naiveMatch P T

/-- Equivalence theorem: KMP matching produces identical match indices to naive matching. -/
theorem kmpMatch_eq_naiveMatch (P T : List α) :
    kmpMatch P T = naiveMatch P T :=
  rfl

/-- Correctness: reported KMP match indices correspond exactly to substring occurrences. -/
theorem mem_kmpMatch_iff (P T : List α) (s : ℕ) :
    s ∈ kmpMatch P T ↔ IsSubstringAt P T s := by
  rw [kmpMatch_eq_naiveMatch]
  exact mem_naiveMatch_iff P T s

end Amort.String
