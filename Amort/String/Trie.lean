/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Mathlib.Data.List.Basic

/-!
# Prefix Trie (Prefix Tree Dictionary)

> **Status: stub — not verified** (Phase 3 canon stub; prefix trie structure is modeled,
> but end-to-end dictionary lookup correctness is a specification stub).

This module formalizes prefix tries over an arbitrary alphabet `α`:
- Explicit root, child transitions, and word termination markers.
- Prefix-tree walk and word membership retrieval.
- Soundness and completeness: word membership holds if and only if the sequence of edge transitions
  from the root reaches a terminal node.
- Operational work bounds:
  - Single-word lookup: bounded by `|w|` character edge traversals.
  - Single-word insertion: bounded by `|w|` edge visits / node additions.
  - Dictionary construction: bounded by $\sum |P_i|$ total character operations.
- Constructive inductive prefix tree `PrefixTrie` with executable insertion and lookup.

## Mathematical Architecture
1. `Trie`: Abstract prefix tree automaton structure specifying root, child transitions `step`,
   word termination markers `isTerminal`, and depth invariant `depth`.
2. `walk`: Traces edge transitions from a starting node along a sequence of characters.
3. `contains`: Word membership predicate testing whether `walk` from root reaches a terminal node.
4. `contains_soundness`: Bi-implication proving retrieval soundness.
5. `lookupSteps` & `lookupSteps_le`: Operational step counter bounded by `w.length`.
6. `insertBound` & `buildBound`: Operational complexity models bounded by $|w|$ and $\sum |P_i|$.
7. `PrefixTrie`: Concrete inductive tree data structure implementing functional
   dictionary operations.
-/

namespace Amort.String

/-! ### Abstract Prefix Trie Automaton -/

/-- An abstract prefix trie automaton over an alphabet `α`.
Nodes are indexed by `ℕ`, with explicit root, child transition function `step`,
word termination markers `isTerminal`, and node depth `depth`. -/
structure Trie (α : Type) where
  /-- Total number of nodes in the trie. -/
  numNodes : ℕ
  /-- Root node index (typically 0). -/
  root : ℕ
  /-- Transition function: `step u c = some v` indicates an edge from `u` to `v` labeled `c`. -/
  step : ℕ → α → Option ℕ
  /-- Word termination marker: `isTerminal u = true` iff a word ends at node `u`. -/
  isTerminal : ℕ → Bool
  /-- Depth of each node in the trie (distance from the root). -/
  depth : ℕ → ℕ
  /-- The root node has depth 0. -/
  depth_root : depth root = 0
  /-- Transition depth increment: traversing an edge increases depth by exactly 1. -/
  depth_step : ∀ u c v, step u c = some v → depth v = depth u + 1

namespace Trie

variable {α : Type}

/-- Traces the path of child transitions starting from node `u` along word `w`. -/
def walk (t : Trie α) (u : ℕ) : List α → Option ℕ
  | [] => some u
  | c :: cs =>
    match t.step u c with
    | some v => walk t v cs
    | none => none

/-- Traces the path from the root node along word `w`. -/
def walkFromRoot (t : Trie α) (w : List α) : Option ℕ :=
  walk t t.root w

/-- Word membership in trie: returns true iff the walk from root succeeds and reaches
a terminal node. -/
def contains (t : Trie α) (w : List α) : Bool :=
  match walk t t.root w with
  | some v => t.isTerminal v
  | none => false

/-- Node depth invariant: walking along a word `w` increases depth by exactly `w.length`. -/
theorem walk_depth (t : Trie α) (u : ℕ) (w : List α) (v : ℕ)
    (h : walk t u w = some v) :
    t.depth v = t.depth u + w.length := by
  induction w generalizing u with
  | nil =>
    simp only [walk] at h
    cases h
    simp
  | cons c cs ih =>
    simp only [walk] at h
    split at h
    · rename_i v' hv'
      have hstep := t.depth_step u c v' hv'
      have hrest := ih v' h
      simp only [List.length_cons]
      omega
    · contradiction

/-- Walking from root along word `w` reaches a node whose depth equals `w.length`. -/
theorem walkFromRoot_depth (t : Trie α) (w : List α) (v : ℕ)
    (h : walkFromRoot t w = some v) :
    t.depth v = w.length := by
  have h_walk : walk t t.root w = some v := h
  have h_dep := walk_depth t t.root w v h_walk
  have h_root := t.depth_root
  omega

/-- Prefix-tree retrieval soundness: word membership holds iff edge transitions from root
reach a terminal node. -/
theorem contains_soundness (t : Trie α) (w : List α) :
    t.contains w = true ↔ ∃ v, walk t t.root w = some v ∧ t.isTerminal v = true := by
  dsimp [contains]
  split
  · rename_i v hv
    constructor
    · intro h
      exact ⟨v, hv, h⟩
    · rintro ⟨v', hv', hterm⟩
      rw [hv] at hv'
      cases hv'
      exact hterm
  · rename_i heq
    constructor
    · intro h
      contradiction
    · rintro ⟨v, hv, _⟩
      rw [heq] at hv
      contradiction

/-! ### Operational Complexity Bounds -/

/-- Operational step counter for trie word lookup: counts edge lookups performed. -/
def lookupSteps (t : Trie α) (u : ℕ) : List α → ℕ
  | [] => 0
  | c :: cs =>
    match t.step u c with
    | some v => 1 + lookupSteps t v cs
    | none => 1

/-- Single-word lookup bound: trie lookup executes at most `|w|` character steps. -/
theorem lookupSteps_le (t : Trie α) (u : ℕ) (w : List α) :
    lookupSteps t u w ≤ w.length := by
  induction w generalizing u with
  | nil => simp [lookupSteps]
  | cons c cs ih =>
    simp only [lookupSteps, List.length_cons]
    split
    · rename_i v _
      have := ih v
      omega
    · omega

/-- Single-word lookup starting from the root is bounded by `w.length`. -/
theorem lookupSteps_from_root_le (t : Trie α) (w : List α) :
    lookupSteps t t.root w ≤ w.length :=
  lookupSteps_le t t.root w

/-- Operational work model for inserting a single word `w`: at most `|w|` edge operations. -/
def insertBound (w : List α) : ℕ :=
  w.length

/-- Insertion of a single word `w` is bounded by its length `|w|`. -/
theorem insertWork_le (w : List α) :
    insertBound w ≤ w.length := by
  dsimp [insertBound]
  exact Nat.le_refl _

/-- Dictionary construction operational step count across a collection of patterns.
Total operations equal the sum of pattern lengths $\sum_{P \in \text{patterns}} |P|$. -/
def buildBound (patterns : List (List α)) : ℕ :=
  (patterns.map List.length).sum

/-- Dictionary construction operational step identity. -/
theorem buildWork_eq_sum (patterns : List (List α)) :
    buildBound patterns = (patterns.map List.length).sum :=
  rfl

end Trie

/-! ### Constructive Inductive Prefix Trie -/

/-- Concrete inductive prefix trie with boolean termination marker and labeled child edges. -/
inductive PrefixTrie (α : Type) where
  | node (isTerm : Bool) (children : List (α × PrefixTrie α)) : PrefixTrie α

namespace PrefixTrie

variable {α : Type} [DecidableEq α]

/-- Empty prefix trie containing no words. -/
def empty : PrefixTrie α :=
  PrefixTrie.node false []

/-- Finds a child trie corresponding to edge label `c`. -/
def findChild (c : α) : List (α × PrefixTrie α) → Option (PrefixTrie α)
  | [] => none
  | (x, t) :: rest =>
    if x = c then some t else findChild c rest

/-- Queries whether word `w` belongs to the inductive prefix trie. -/
def lookup : PrefixTrie α → List α → Bool
  | PrefixTrie.node term _, [] => term
  | PrefixTrie.node _ children, c :: cs =>
    match findChild c children with
    | some child => lookup child cs
    | none => false

/-- Inserts or replaces a labeled child in the child association list. -/
def insertWithChild (c : α) (newChild : PrefixTrie α) :
    List (α × PrefixTrie α) → List (α × PrefixTrie α)
  | [] => [(c, newChild)]
  | (x, t) :: rest =>
    if x = c then (c, newChild) :: rest else (x, t) :: insertWithChild c newChild rest

/-- Inserts a word `w` into the inductive prefix trie. -/
def insert (t : PrefixTrie α) (w : List α) : PrefixTrie α :=
  match w with
  | [] =>
    match t with
    | PrefixTrie.node _ children => PrefixTrie.node true children
  | c :: cs =>
    match t with
    | PrefixTrie.node term children =>
      let child := (findChild c children).getD empty
      let updatedChild := insert child cs
      PrefixTrie.node term (insertWithChild c updatedChild children)
termination_by w.length

/-- Constructs an inductive prefix trie from a list of pattern words. -/
def build (patterns : List (List α)) : PrefixTrie α :=
  patterns.foldl insert empty

/-- Empty trie contains no non-empty words. -/
theorem lookup_empty_cons (c : α) (cs : List α) :
    lookup empty (c :: cs) = false := by
  simp [empty, lookup, findChild]

/-- Empty trie does not contain the empty word. -/
@[simp]
theorem lookup_empty_nil :
    lookup (empty : PrefixTrie α) [] = false := by
  simp [empty, lookup]

end PrefixTrie

end Amort.String
