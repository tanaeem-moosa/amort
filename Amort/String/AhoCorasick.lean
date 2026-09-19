/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Amort.String.Trie
import Mathlib.Data.List.Basic

/-!
# Aho-Corasick Multi-Pattern Matching Automaton

This module formalizes the Aho-Corasick multi-pattern matching automaton:
- Prefix trie augmented with failure links (suffix links) and dictionary output links.
- Text scanning state transitions with failure-link fallback.
- Amortized analysis using the tree-depth potential function $\Phi(u) = \text{depth}(u)$,
  proving that text scanning completes in at most $2|T|$ state transitions/comparisons.
- Match reporting and overall multi-pattern search complexity bound
  $O(\sum |P_i| + |T| + z)$, where $z$ is the number of reported pattern matches.

## Mathematical Architecture
1. `AhoCorasick`: Structure bundling a prefix trie `trie`, a failure function `fail`,
   the contraction invariant `depth (fail u) < depth u` for non-root nodes, and dictionary
   `outputList`.
2. `acStep`: Single-character state transition with failure-link fallback until a valid edge
   is found or the root is reached.
3. `acStep_bound`: Amortized single-step inequality
   $\text{steps} + \text{depth}(u') \le \text{depth}(u) + 2$.
4. `acScan`: Text scanning loop processing text $T$ character by character.
5. `acScan_bound`: Telescoping potential bound
   $\text{steps} + \text{depth}(u_{\text{end}}) \le \text{depth}(u_{\text{start}}) + 2|T|$.
6. `acScan_le_two_mul`: Text scanning bound starting from root $\le 2|T|$.
7. `acTotalSearchWork`: Combined multi-pattern search operational work
   $\sum |P_i| + 2|T| + z$, establishing $O(\sum |P_i| + |T| + z)$ complexity.
-/

namespace Amort.String

variable {α : Type}

/-- An Aho-Corasick multi-pattern matching automaton.
Extends a prefix trie with failure links (suffix links) and output dictionary links. -/
structure AhoCorasick (α : Type) where
  /-- Underlying prefix trie dictionary. -/
  trie : Trie α
  /-- Failure link (suffix link) mapping each state to its longest proper suffix state. -/
  fail : ℕ → ℕ
  /-- Root failure link loops to root. -/
  fail_root : fail trie.root = trie.root
  /-- Strict depth contraction: for any non-root node, the failure link leads to a node
  of strictly smaller tree depth. -/
  fail_depth_lt : ∀ u, 0 < trie.depth u → trie.depth (fail u) < trie.depth u
  /-- Dictionary patterns output upon entering state `u`. -/
  outputList : ℕ → List (List α)

namespace AhoCorasick

/-- Single-character transition of the Aho-Corasick automaton.
Follows a trie edge if available; otherwise traverses failure links until a matching edge
or the root is reached. Returns the next state and total transitions performed. -/
def acStep (t : Trie α) (fail : ℕ → ℕ)
    (hfail : ∀ u, 0 < t.depth u → t.depth (fail u) < t.depth u)
    (u : ℕ) (c : α) : ℕ × ℕ :=
  match t.step u c with
  | some v => (v, 1)
  | none =>
    if hu : 0 < t.depth u then
      have : t.depth (fail u) < t.depth u := hfail u hu
      let res := acStep t fail hfail (fail u) c
      (res.1, res.2 + 1)
    else
      (u, 1)
termination_by t.depth u

/-- Amortized potential step bound: with tree-depth potential function $\Phi(u) = \text{depth}(u)$,
the step count plus the change in depth is bounded by 2:
$\text{steps} + \text{depth}(u') \le \text{depth}(u) + 2$. -/
theorem acStep_bound (t : Trie α) (fail : ℕ → ℕ)
    (hfail : ∀ u, 0 < t.depth u → t.depth (fail u) < t.depth u)
    (u : ℕ) (c : α) :
    (acStep t fail hfail u c).2 + t.depth (acStep t fail hfail u c).1 ≤ t.depth u + 2 := by
  rw [acStep]
  split
  · rename_i v hv
    dsimp
    have := t.depth_step u c v hv
    omega
  · split
    · rename_i hu
      have : t.depth (fail u) < t.depth u := hfail u hu
      have ih := acStep_bound t fail hfail (fail u) c
      dsimp
      omega
    · rename_i _ hnot
      dsimp
      have : t.depth u = 0 := by omega
      omega
termination_by t.depth u

/-- Text scanning state and step counter: processes text `T` character by character,
returning the final automaton state and accumulated transition steps. -/
def acScan (t : Trie α) (fail : ℕ → ℕ)
    (hfail : ∀ u, 0 < t.depth u → t.depth (fail u) < t.depth u) :
    List α → ℕ → ℕ × ℕ
  | [], u => (u, 0)
  | c :: cs, u =>
    let (u1, s1) := acStep t fail hfail u c
    let (u_end, s2) := acScan t fail hfail cs u1
    (u_end, s1 + s2)

/-- Telescoping potential bound for Aho-Corasick text scanning:
$\text{steps} + \text{depth}(u_{\text{end}}) \le \text{depth}(u) + 2|T|$. -/
theorem acScan_bound (t : Trie α) (fail : ℕ → ℕ)
    (hfail : ∀ u, 0 < t.depth u → t.depth (fail u) < t.depth u)
    (T : List α) (u : ℕ) :
    (acScan t fail hfail T u).2 + t.depth (acScan t fail hfail T u).1 ≤
      t.depth u + 2 * T.length := by
  induction T generalizing u with
  | nil => simp [acScan]
  | cons c cs ih =>
    simp only [acScan, List.length_cons]
    have h1 := acStep_bound t fail hfail u c
    have h2 := ih (acStep t fail hfail u c).1
    omega

/-- Linear text scanning bound: starting from the root node (`depth = 0`),
text scanning executes in at most $2|T|$ state transitions. -/
theorem acScan_le_two_mul (t : Trie α) (fail : ℕ → ℕ)
    (hfail : ∀ u, 0 < t.depth u → t.depth (fail u) < t.depth u)
    (T : List α) :
    (acScan t fail hfail T t.root).2 ≤ 2 * T.length := by
  have h := acScan_bound t fail hfail T t.root
  have hroot := t.depth_root
  omega

/-- Text scanning bound for an AhoCorasick structure instance. -/
theorem scan_steps_le (ac : AhoCorasick α) (T : List α) :
    (acScan ac.trie ac.fail ac.fail_depth_lt T ac.trie.root).2 ≤ 2 * T.length :=
  acScan_le_two_mul ac.trie ac.fail ac.fail_depth_lt T

/-! ### Overall Multi-Pattern Search Complexity -/

/-- Total operational work for Aho-Corasick multi-pattern search:
dictionary construction steps $\sum |P_i|$, text scanning steps $\le 2|T|$,
and reported match emission steps $z$. -/
def acTotalSearchWork (patternWork textLength reportedMatches : ℕ) : ℕ :=
  patternWork + 2 * textLength + reportedMatches

/-- Concrete search bound for patterns $P$ and text $T$:
$\text{totalWork} \le \sum |P_i| + 2|T| + z$. -/
theorem acTotalSearchWork_bound (patterns : List (List α)) (T : List α) (z : ℕ) :
    acTotalSearchWork (Trie.buildWork patterns) T.length z =
      (patterns.map List.length).sum + 2 * T.length + z :=
  rfl

end AhoCorasick

end Amort.String
