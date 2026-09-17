/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Ring

/-!
# Binary Decision Trees for Comparison-Based Algorithms

This module formalizes abstract binary decision trees used to model comparison-based algorithms
(and specifically comparison-based sorting).

## Mathematical Overview
A comparison-based algorithm is modeled as an abstract binary decision tree:
- Internal nodes query an oracle with a question of type `α` (e.g. comparing indices `(i, j)`).
- Leaves store an output of type `β` (e.g. a permutation of indices or a sorted list).
- At each step, a boolean answer chooses the left branch (`true`) or right branch (`false`).

The depth of the tree corresponds to the worst-case number of comparisons executed along any path.
By structural induction, any binary tree of depth `d` has at most `2 ^ d` leaves:
$$\text{leafCount}(T) \le 2^{\text{depth}(T)}$$

## Main Definitions and Theorems
- `Amort.Sorting.DecisionTree`: Inductive datatype of binary decision trees.
- `Amort.Sorting.DecisionTree.depth`: Height or worst-case query count.
- `Amort.Sorting.DecisionTree.leafCount`: Total number of leaves in the tree.
- `Amort.Sorting.DecisionTree.leafCount_le_two_pow_depth`: Proof that `leafCount T ≤ 2 ^ depth T`.
- `Amort.Sorting.DecisionTree.eval`: Evaluates the tree on a given query oracle `α → Bool`.
- `Amort.Sorting.DecisionTree.leavesList`: List of all leaf values in the tree.
- `Amort.Sorting.DecisionTree.leaves`: Finset of distinct leaf values.
- `Amort.Sorting.DecisionTree.card_leaves_le_two_pow_depth`: Leaf set bound `≤ 2 ^ depth T`.
-/

namespace Amort.Sorting

/-- An abstract binary decision tree.
* `α` is the query/comparison type.
* `β` is the outcome/result type at the leaves. -/
inductive DecisionTree (α : Type u) (β : Type v) where
  | leaf (val : β) : DecisionTree α β
  | node (query : α) (left right : DecisionTree α β) : DecisionTree α β
  deriving Repr

namespace DecisionTree

variable {α : Type u} {β : Type v}

/-- The depth (height or worst-case query count) of a decision tree. -/
def depth : DecisionTree α β → ℕ
  | leaf _ => 0
  | node _ left right => max (depth left) (depth right) + 1

/-- The total number of leaves in a decision tree. -/
def leafCount : DecisionTree α β → ℕ
  | leaf _ => 1
  | node _ left right => leafCount left + leafCount right

/-- The fundamental structural induction bound: any binary decision tree of depth `d`
has at most `2 ^ d` leaves. -/
theorem leafCount_le_two_pow_depth (T : DecisionTree α β) :
    leafCount T ≤ 2 ^ depth T := by
  induction T with
  | leaf val =>
    simp [leafCount, depth]
  | node query left right ih_l ih_r =>
    simp only [leafCount, depth]
    have h_l : leafCount left ≤ 2 ^ max (depth left) (depth right) :=
      ih_l.trans (Nat.pow_le_pow_right (by decide) (le_max_left _ _))
    have h_r : leafCount right ≤ 2 ^ max (depth left) (depth right) :=
      ih_r.trans (Nat.pow_le_pow_right (by decide) (le_max_right _ _))
    have h_two : 2 ^ max (depth left) (depth right) + 2 ^ max (depth left) (depth right) =
        2 * 2 ^ max (depth left) (depth right) := by ring
    calc leafCount left + leafCount right
      _ ≤ 2 ^ max (depth left) (depth right) + 2 ^ max (depth left) (depth right) :=
        Nat.add_le_add h_l h_r
      _ = 2 * 2 ^ max (depth left) (depth right) := h_two
      _ = 2 ^ (max (depth left) (depth right) + 1) := by rw [Nat.pow_succ', mul_comm]

/-- Execution/evaluation of a decision tree given an evaluation oracle for queries. -/
def eval (T : DecisionTree α β) (oracle : α → Bool) : β :=
  match T with
  | leaf val => val
  | node query left right =>
    if oracle query then eval left oracle else eval right oracle

/-- The list of all leaf values occurring in a decision tree (with multiplicity). -/
def leavesList : DecisionTree α β → List β
  | leaf val => [val]
  | node _ left right => leavesList left ++ leavesList right

@[simp]
theorem length_leavesList (T : DecisionTree α β) :
    (leavesList T).length = leafCount T := by
  induction T with
  | leaf val => rfl
  | node query left right ih_l ih_r =>
    simp [leavesList, leafCount, ih_l, ih_r]

/-- Every execution of a decision tree on an oracle terminates at a leaf in `leavesList T`. -/
theorem eval_mem_leavesList (T : DecisionTree α β) (oracle : α → Bool) :
    eval T oracle ∈ leavesList T := by
  induction T with
  | leaf val =>
    simp [eval, leavesList]
  | node query left right ih_l ih_r =>
    simp only [eval, leavesList, List.mem_append]
    split_ifs
    · exact Or.inl ih_l
    · exact Or.inr ih_r

/-- The finset of distinct leaf values occurring in a decision tree. -/
def leaves [DecidableEq β] (T : DecisionTree α β) : Finset β :=
  (leavesList T).toFinset

/-- The number of distinct leaf outcomes is bounded by the total leaf count. -/
theorem card_leaves_le_leafCount [DecidableEq β] (T : DecisionTree α β) :
    (leaves T).card ≤ leafCount T := by
  rw [leaves, ← length_leavesList]
  exact List.toFinset_card_le _

/-- The number of distinct leaf outcomes is bounded by `2 ^ depth T`. -/
theorem card_leaves_le_two_pow_depth [DecidableEq β] (T : DecisionTree α β) :
    (leaves T).card ≤ 2 ^ depth T :=
  (card_leaves_le_leafCount T).trans (leafCount_le_two_pow_depth T)

/-- Any evaluation of a decision tree terminates at a leaf in `leaves T`. -/
theorem eval_mem_leaves [DecidableEq β] (T : DecisionTree α β) (oracle : α → Bool) :
    eval T oracle ∈ leaves T := by
  simp [leaves, eval_mem_leavesList]

end DecisionTree

end Amort.Sorting
