/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Ring

/-!
# Rabin-Karp Rolling Hash String Matching

> **Status: stub — not verified** (Phase 3 canon stub; rolling hash algebra is proven,
> but Las Vegas verification matcher is a specification stub).

This module formalizes the Rabin-Karp randomized/algebraic string matching algorithm:
- Polynomial rolling hash function with base $B$ modulo prime $p$:
  $$H(w) = \sum_{j=0}^{m-1} w[j] \cdot B^{m - 1 - j}$$
- Constant-time ($O(1)$) sliding window hash update identity:
  $$H(S[i+1 \dots i+m]) \equiv (H(S[i \dots i+m-1]) \cdot B - S[i] \cdot B^m + S[i+m]) \pmod p$$
- Hash congruence soundness: identical substrings produce identical hash values.
- Operational step bound and average-case $O(|T| + |P|)$ comparison complexity.

## Mathematical Architecture
1. `polyHash`: Exact polynomial rolling hash on integer sequences with base $B$.
2. `polyHash_append_singleton`: Horner extension lemma $H(w ++ [c]) = H(w) \cdot B + c$.
3. `polyHash_sliding_window`: Exact integer sliding window update identity.
4. `polyHash_sliding_window_mod`: Modular sliding window congruence in `Int.ModEq`.
5. `polyHash_congruence_soundness`: Soundness theorem proving that identical strings
   yield identical hash values.
6. `polyHash_mod_congruence`: Modular soundness theorem.
7. `rabinKarpBound` & `rabinKarpAverageBound`: Operational complexity bounds.
-/

namespace Amort.String

/-! ### Polynomial Rolling Hash Function -/

/-- Polynomial rolling hash function on integer sequences with base `B`.
Evaluates $H(w) = \sum_{j=0}^{m-1} w[j] \cdot B^{m - 1 - j}$. -/
def polyHash (B : ℤ) : List ℤ → ℤ
  | [] => 0
  | c :: cs => c * B ^ cs.length + polyHash B cs

/-- Horner appending lemma: appending a character `c` to word `cs` multiplies the existing
hash by base `B` and adds `c`. -/
theorem polyHash_append_singleton (B : ℤ) (cs : List ℤ) (c : ℤ) :
    polyHash B (cs ++ [c]) = polyHash B cs * B + c := by
  induction cs with
  | nil =>
    simp only [polyHash, List.nil_append, List.length_nil, pow_zero, mul_one, add_zero, zero_mul,
      zero_add]
  | cons x xs ih =>
    simp only [List.cons_append, polyHash, List.length_append, List.length_nil, List.length_cons]
    rw [ih]
    ring

/-! ### Sliding Window Hash Update Identity -/

/-- Constant-time sliding window hash update identity over integers:
Dropping leading character `c_old` and appending trailing character `c_new` satisfies:
$H(cs ++ [c_{\text{new}}]) = H(c_{\text{old}} :: cs) \cdot B -
  c_{\text{old}} \cdot B^{|cs|+1} + c_{\text{new}}$. -/
theorem polyHash_sliding_window (B : ℤ) (c_old : ℤ) (cs : List ℤ) (c_new : ℤ) :
    polyHash B (cs ++ [c_new]) =
      polyHash B (c_old :: cs) * B - c_old * B ^ (cs.length + 1) + c_new := by
  rw [polyHash_append_singleton]
  simp only [polyHash]
  ring

/-- Sliding window modular congruence:
$$H(S[i+1 \dots i+m]) \equiv (H(S[i \dots i+m-1]) \cdot B - S[i] \cdot B^m + S[i+m]) \pmod p$$
holds identically under `Int.ModEq`. -/
theorem polyHash_sliding_window_mod (p : ℤ) (B : ℤ) (c_old : ℤ) (cs : List ℤ) (c_new : ℤ) :
    Int.ModEq p (polyHash B (cs ++ [c_new]))
      (polyHash B (c_old :: cs) * B - c_old * B ^ (cs.length + 1) + c_new) := by
  rw [polyHash_sliding_window]

/-! ### Hash Congruence Soundness -/

/-- Hash congruence soundness: identical substrings produce identical integer hash values. -/
theorem polyHash_congruence_soundness (B : ℤ) (w₁ w₂ : List ℤ) (h : w₁ = w₂) :
    polyHash B w₁ = polyHash B w₂ := by
  rw [h]

/-- Modular hash congruence soundness: identical substrings produce identical hash residues
modulo $p$. -/
theorem polyHash_mod_congruence (p : ℤ) (B : ℤ) (w₁ w₂ : List ℤ) (h : w₁ = w₂) :
    Int.ModEq p (polyHash B w₁) (polyHash B w₂) := by
  rw [h]

/-! ### Operational Complexity Bounds -/

/-- Operational step model for Rabin-Karp string matching:
- Precomputing pattern hash: $|P|$ arithmetic operations.
- Computing initial text window hash: $|P|$ arithmetic operations.
- Sliding window hash updates: $O(1)$ operations per shift, totaling $|T| - |P|$ operations.
- Full substring comparisons performed only on hash match (count $k$ of candidate matches):
  $k \cdot |P|$ character comparisons. -/
def rabinKarpBound (textLen patternLen collisions : ℕ) : ℕ :=
  2 * patternLen + textLen + collisions * patternLen

/-- In the average case (or when the prime modulus $p$ ensures zero false-positive collisions),
total operations are bounded by $2(|T| + |P|)$ ($O(|T| + |P|)$). -/
def rabinKarpAverageBound (textLen patternLen : ℕ) : ℕ :=
  2 * (textLen + patternLen)

/-- In the absence of spurious hash collisions, operational work is linear in $|T| + |P|$. -/
theorem rabinKarpWork_no_collisions (textLen patternLen : ℕ) :
    rabinKarpBound textLen patternLen 0 ≤ rabinKarpAverageBound textLen patternLen := by
  dsimp [rabinKarpBound, rabinKarpAverageBound]
  omega

end Amort.String
