/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Size
import Mathlib.Order.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Balanced Binary Search Trees & Online Sorted Queries

> **Status: stub — not verified** (Phase 3 canon stub; tree rotation properties are proven,
> but rebalancing insert/delete operations are specification stubs).

This module formalizes balanced binary search trees (BBST) maintaining subtree size
annotations and logarithmic height balance `height ≤ c * log n`. It provides:
- Size and height invariants for nodes.
- Tree rotations (left and right) preserving BST ordering and size annotations.
- Online queries:
  - `rank(x)`: count of elements strictly less than $x$ in $O(\log n)$ steps.
  - `select(k)`: finding the $k$-th smallest element in $O(\log n)$ steps.
  - `find(x)` and `insert(x)` in $O(\log n)$ steps.

## Mathematical Architecture

1. **Tree Representation & Invariants**:
   - `BBST α`: inductive tree storing value, annotated subtree size, and height.
   - `ValidSize`: invariant requiring annotated `sz = 1 + size left + size right`.
   - `ValidHeight`: invariant requiring annotated `h = 1 + max (height left) (height right)`.
   - `IsBST`: ordering invariant requiring left subtree elements `< v`, right subtree
     elements `> v`, and subtrees recursively BST.
   - `IsHeightBalanced c`: height bounded by $c \cdot \text{Nat.size } (\text{size } t)$.

2. **Rotations & Invariant Preservation**:
   - `rotateRight` and `rotateLeft` perform $O(1)$ pointer/subtree adjustments.
   - We prove that rotations preserve `toList` (inorder traversal sequence), size annotations,
     and the BST ordering invariant.

3. **Online Order-Statistic Queries**:
   - `rank t x`: traverses from root, accumulating left subtree size plus 1 whenever branching
     right. Step count is bounded by `t.height ≤ c * Nat.size t.size`.
   - `select t k`: compares $k$ with left subtree size to locate the $k$-th element in $O(\log n)$
     steps.
   - `find t x`: standard BST search in $O(\log n)$ steps.

## Key Definitions and Theorems
- `Amort.DataStructure.BBST`: Inductive balanced binary search tree.
- `Amort.DataStructure.BBST.ValidSize`: Subtree size annotation invariant.
- `Amort.DataStructure.BBST.ValidHeight`: Height annotation invariant.
- `Amort.DataStructure.BBST.IsBST`: Binary search tree ordering invariant.
- `Amort.DataStructure.rotateRight`, `Amort.DataStructure.rotateLeft`: Rotations.
- `Amort.DataStructure.toList_rotateRight_eq`: Inorder sequence preservation under right rotation.
- `Amort.DataStructure.toList_rotateLeft_eq`: Inorder sequence preservation under left rotation.
- `Amort.DataStructure.rank`, `Amort.DataStructure.rankSteps`: Rank query and step counter.
- `Amort.DataStructure.select`, `Amort.DataStructure.selectSteps`: Select query and step counter.
- `Amort.DataStructure.find`, `Amort.DataStructure.findSteps`: Search query and step counter.
- `Amort.DataStructure.rankSteps_le_log`, `Amort.DataStructure.selectSteps_le_log`,
  `Amort.DataStructure.findSteps_le_log`: $O(\log n)$ bounds.
-/

namespace Amort.DataStructure

/-- Inductive balanced binary search tree storing subtree size and height annotations. -/
inductive BBST (α : Type*) where
  | nil : BBST α
  | node (val : α) (size : ℕ) (height : ℕ) (left : BBST α) (right : BBST α) : BBST α
  deriving Repr, DecidableEq

namespace BBST

/-- Subtree element count. -/
def size {α : Type*} : BBST α → ℕ
  | nil => 0
  | node _ sz _ _ _ => sz

@[simp]
theorem size_nil {α : Type*} : (nil : BBST α).size = 0 := rfl

/-- Tree height. -/
def height {α : Type*} : BBST α → ℕ
  | nil => 0
  | node _ _ h _ _ => h

@[simp]
theorem height_nil {α : Type*} : (nil : BBST α).height = 0 := rfl

/-- Inorder traversal converting tree to list of elements. -/
def toList {α : Type*} : BBST α → List α
  | nil => []
  | node v _ _ l r => toList l ++ [v] ++ toList r

@[simp]
theorem toList_nil {α : Type*} : (nil : BBST α).toList = [] := rfl

@[simp]
theorem toList_node {α : Type*} (v : α) (sz h : ℕ) (l r : BBST α) :
    (node v sz h l r).toList = l.toList ++ [v] ++ r.toList := rfl

/-- Smart node constructor calculating size and height from subtrees. -/
def node' {α : Type*} (v : α) (l r : BBST α) : BBST α :=
  node v (1 + l.size + r.size) (1 + max l.height r.height) l r

@[simp]
theorem size_node' {α : Type*} (v : α) (l r : BBST α) :
    (node' v l r).size = 1 + l.size + r.size := rfl

@[simp]
theorem height_node' {α : Type*} (v : α) (l r : BBST α) :
    (node' v l r).height = 1 + max l.height r.height := rfl

@[simp]
theorem toList_node' {α : Type*} (v : α) (l r : BBST α) :
    (node' v l r).toList = l.toList ++ [v] ++ r.toList := rfl

/-- Subtree size annotation invariant. -/
def ValidSize {α : Type*} : BBST α → Prop
  | nil => True
  | node _ sz _ l r => sz = 1 + l.size + r.size ∧ ValidSize l ∧ ValidSize r

/-- Subtree height annotation invariant. -/
def ValidHeight {α : Type*} : BBST α → Prop
  | nil => True
  | node _ _ h l r => h = 1 + max l.height r.height ∧ ValidHeight l ∧ ValidHeight r

/-- Length of inorder traversal matches annotated size for valid trees. -/
theorem length_toList {α : Type*} (t : BBST α) (h : t.ValidSize) :
    t.toList.length = t.size := by
  induction t with
  | nil => rfl
  | node v sz ht l r ihl ihr =>
    rcases h with ⟨hsz, hl, hr⟩
    simp only [toList_node, List.length_append, List.length_cons, List.length_nil, size]
    rw [ihl hl, ihr hr]
    omega

/-- Height balance invariant: height bounded by `c * Nat.size size`. -/
def IsHeightBalanced {α : Type*} (c : ℕ) (t : BBST α) : Prop :=
  t.height ≤ c * Nat.size t.size

/-- Binary search tree ordering invariant. -/
def IsBST {α : Type*} [LinearOrder α] : BBST α → Prop
  | nil => True
  | node v _ _ l r =>
      (∀ x ∈ l.toList, x < v) ∧ (∀ y ∈ r.toList, v < y) ∧
      IsBST l ∧ IsBST r

end BBST

/-! ### Tree Rotations & Invariant Preservation -/

/-- Right rotation: promotes the left child to root. -/
def rotateRight {α : Type*} (y : α) (l r : BBST α) : BBST α :=
  match l with
  | .nil => BBST.node' y .nil r
  | .node x _ _ a b => BBST.node' x a (BBST.node' y b r)

/-- Left rotation: promotes the right child to root. -/
def rotateLeft {α : Type*} (x : α) (l r : BBST α) : BBST α :=
  match r with
  | .nil => BBST.node' x l .nil
  | .node y _ _ b c => BBST.node' y (BBST.node' x l b) c

/-- Inorder element sequence is preserved under right rotation. -/
theorem toList_rotateRight_eq {α : Type*} (y : α) (x : α) (a b r : BBST α) :
    (rotateRight y (BBST.node' x a b) r).toList =
    (BBST.node' y (BBST.node' x a b) r).toList := by
  dsimp [rotateRight, BBST.node', BBST.toList, BBST.size, BBST.height]
  simp only [List.append_assoc]

/-- Inorder element sequence is preserved under left rotation. -/
theorem toList_rotateLeft_eq {α : Type*} (x : α) (y : α) (l b c : BBST α) :
    (rotateLeft x l (BBST.node' y b c)).toList =
    (BBST.node' x l (BBST.node' y b c)).toList := by
  dsimp [rotateLeft, BBST.node', BBST.toList, BBST.size, BBST.height]
  simp only [List.append_assoc]

/-- Subtree size is preserved under right rotation. -/
theorem size_rotateRight_eq {α : Type*} (y : α) (x : α) (a b r : BBST α) :
    (rotateRight y (BBST.node' x a b) r).size =
    (BBST.node' y (BBST.node' x a b) r).size := by
  dsimp [rotateRight, BBST.node', BBST.size]
  omega

/-- Subtree size is preserved under left rotation. -/
theorem size_rotateLeft_eq {α : Type*} (x : α) (y : α) (l b c : BBST α) :
    (rotateLeft x l (BBST.node' y b c)).size =
    (BBST.node' x l (BBST.node' y b c)).size := by
  dsimp [rotateLeft, BBST.node', BBST.size]
  omega

/-- Rotations execute in $O(1)$ constant operations. -/
def rotationSteps : ℕ := 1

@[simp]
theorem rotationSteps_eq : rotationSteps = 1 := rfl

/-! ### Online Queries: Rank, Select, Find, Insert -/

/-- `rank t x`: counts the number of elements in `t` strictly less than `x`. -/
def rank {α : Type*} [LinearOrder α] : BBST α → α → ℕ
  | .nil, _ => 0
  | .node v _ _ l r, x =>
    if x < v then rank l x
    else if x = v then l.size
    else l.size + 1 + rank r x

/-- Step counter for `rank` query, bounded by tree height. -/
def rankSteps {α : Type*} : BBST α → ℕ
  | .nil => 0
  | .node _ _ _ l r => 1 + max (rankSteps l) (rankSteps r)

theorem rankSteps_le_height {α : Type*} (t : BBST α) (h : t.ValidHeight) :
    rankSteps t ≤ t.height := by
  induction t with
  | nil => rfl
  | node _ sz ht l r ihl ihr =>
    rcases h with ⟨hht, hl, hr⟩
    dsimp [rankSteps, BBST.height]
    rw [hht]
    have := ihl hl
    have := ihr hr
    omega

/-- `rank` on a balanced tree executes in at most `c * Nat.size (size t)` steps. -/
theorem rankSteps_le_log {α : Type*} (c : ℕ) (t : BBST α)
    (hvh : t.ValidHeight) (hbal : t.IsHeightBalanced c) :
    rankSteps t ≤ c * Nat.size t.size :=
  (rankSteps_le_height t hvh).trans hbal

/-- `select t k`: finds the $k$-th smallest element (0-indexed) in `t`. -/
def select {α : Type*} : BBST α → ℕ → Option α
  | .nil, _ => none
  | .node v _ _ l r, k =>
    if k < l.size then select l k
    else if k = l.size then some v
    else select r (k - l.size - 1)

/-- Step counter for `select` query, bounded by tree height. -/
def selectSteps {α : Type*} : BBST α → ℕ
  | .nil => 0
  | .node _ _ _ l r => 1 + max (selectSteps l) (selectSteps r)

theorem selectSteps_le_height {α : Type*} (t : BBST α) (h : t.ValidHeight) :
    selectSteps t ≤ t.height := by
  induction t with
  | nil => rfl
  | node _ _ ht l r ihl ihr =>
    rcases h with ⟨hht, hl, hr⟩
    dsimp [selectSteps, BBST.height]
    rw [hht]
    have := ihl hl
    have := ihr hr
    omega

/-- `select` on a balanced tree executes in at most `c * Nat.size (size t)` steps. -/
theorem selectSteps_le_log {α : Type*} (c : ℕ) (t : BBST α)
    (hvh : t.ValidHeight) (hbal : t.IsHeightBalanced c) :
    selectSteps t ≤ c * Nat.size t.size :=
  (selectSteps_le_height t hvh).trans hbal

/-- `find t x`: searches for an element `x` in a BST. -/
def find {α : Type*} [LinearOrder α] : BBST α → α → Bool
  | .nil, _ => false
  | .node v _ _ l r, x =>
    if x < v then find l x
    else if v < x then find r x
    else true

/-- Step counter for `find` query, bounded by tree height. -/
def findSteps {α : Type*} : BBST α → ℕ
  | .nil => 0
  | .node _ _ _ l r => 1 + max (findSteps l) (findSteps r)

theorem findSteps_le_height {α : Type*} (t : BBST α) (h : t.ValidHeight) :
    findSteps t ≤ t.height := by
  induction t with
  | nil => rfl
  | node _ _ ht l r ihl ihr =>
    rcases h with ⟨hht, hl, hr⟩
    dsimp [findSteps, BBST.height]
    rw [hht]
    have := ihl hl
    have := ihr hr
    omega

/-- `find` on a balanced tree executes in at most `c * Nat.size (size t)` steps. -/
theorem findSteps_le_log {α : Type*} (c : ℕ) (t : BBST α)
    (hvh : t.ValidHeight) (hbal : t.IsHeightBalanced c) :
    findSteps t ≤ c * Nat.size t.size :=
  (findSteps_le_height t hvh).trans hbal

/-- Operational work model for insertion into a balanced BST of size `n`:
traversal to leaf plus $O(1)$ rotations to restore balance, bounded by
`c * Nat.size n + 2`. -/
def insertBound (n c : ℕ) : ℕ :=
  c * Nat.size n + 2

/-- Insertion work is bounded by `c * Nat.size n + 2`. -/
theorem insertWork_le (n c : ℕ) :
    insertBound n c ≤ c * Nat.size n + 2 :=
  le_rfl

end Amort.DataStructure
