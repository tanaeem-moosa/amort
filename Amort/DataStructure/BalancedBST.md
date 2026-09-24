# Balanced Binary Search Trees & Online Sorted Queries

> **Status: stub — not verified** (Phase 3 canon stub; tree rotation properties are proven,
> but rebalancing insert/delete operations are specification stubs).


This document details the Lean 4 formalization of balanced binary search trees (BBST) with size
annotations in `Amort.DataStructure.BalancedBST`. It establishes tree rotations preserving BST
order and subtree size annotations, and bounds online order-statistic queries (`rank`, `select`,
`find`, `insert`) by $O(\log n)$.

---

## 1. Tree Architecture & Invariant Hierarchy

```lean
inductive BBST (α : Type*) where
  | nil : BBST α
  | node (val : α) (size : ℕ) (height : ℕ) (left : BBST α) (right : BBST α) : BBST α
```

### Invariants
1. **Size Annotation Invariant (`ValidSize`)**:
   Every node stores the exact subtree size:
   $$\text{size}(\text{node } v\ sz\ h\ l\ r) = 1 + \text{size}(l) + \text{size}(r)$$
   Milestone theorem `length_toList` proves that for any valid tree, `t.toList.length = t.size`.

2. **Height Annotation Invariant (`ValidHeight`)**:
   $$\text{height}(\text{node } v\ sz\ h\ l\ r) = 1 + \max(\text{height } l, \text{height } r)$$

3. **BST Ordering Invariant (`IsBST`)**:
   For every node with value $v$, all elements in the left subtree satisfy $x < v$, and all elements
   in the right subtree satisfy $v < y$:
   $$\forall x \in \text{toList } l, x < v \quad \land \quad \forall y \in \text{toList } r, v < y$$

4. **Height Balance Invariant (`IsHeightBalanced c`)**:
   $$\text{height } t \le c \cdot \text{Nat.size } (\text{size } t)$$

---

## 2. Tree Rotations & Invariant Preservation

Tree rotations (left and right) are standard $O(1)$ operations used to restore height balance in
AVL and Red-Black trees.

```lean
def rotateRight (y : α) (l r : BBST α) : BBST α
def rotateLeft (x : α) (l r : BBST α) : BBST α
```

### Inorder Sequence & Size Preservation Theorems
We formally prove that rotations preserve the inorder traversal sequence `toList` and subtree sizes:
```lean
theorem toList_rotateRight_eq (y : α) (x : α) (a b r : BBST α) :
    (rotateRight y (BBST.node' x a b) r).toList =
    (BBST.node' y (BBST.node' x a b) r).toList

theorem toList_rotateLeft_eq (x : α) (y : α) (l b c : BBST α) :
    (rotateLeft x l (BBST.node' y b c)).toList =
    (BBST.node' x l (BBST.node' y b c)).toList

theorem size_rotateRight_eq (y : α) (x : α) (a b r : BBST α) :
    (rotateRight y (BBST.node' x a b) r).size =
    (BBST.node' y (BBST.node' x a b) r).size

theorem size_rotateLeft_eq (x : α) (y : α) (l b c : BBST α) :
    (rotateLeft x l (BBST.node' y b c)).size =
    (BBST.node' x l (BBST.node' y b c)).size
```

---

## 3. Online Order-Statistic Queries ($O(\log n)$)

### `rank(x)` Query
Computes the number of elements strictly smaller than $x$ by inspecting subtree size annotations:
```lean
def rank : BBST α → α → ℕ
  | .nil, _ => 0
  | .node v _ _ l r, x =>
    if x < v then rank l x
    else if x = v then l.size
    else l.size + 1 + rank r x
```
Step counter bound:
```lean
theorem rankSteps_le_log (c : ℕ) (t : BBST α)
    (hvh : t.ValidHeight) (hbal : t.IsHeightBalanced c) :
    rankSteps t ≤ c * Nat.size t.size
```

### `select(k)` Query
Finds the $k$-th smallest element (0-indexed) in $O(\log n)$ steps by comparing $k$ with
$l.\text{size}$:
```lean
def select : BBST α → ℕ → Option α
  | .nil, _ => none
  | .node v _ _ l r, k =>
    if k < l.size then select l k
    else if k = l.size then some v
    else select r (k - l.size - 1)
```
Step counter bound:
```lean
theorem selectSteps_le_log (c : ℕ) (t : BBST α)
    (hvh : t.ValidHeight) (hbal : t.IsHeightBalanced c) :
    selectSteps t ≤ c * Nat.size t.size
```

### `find(x)` and `insert(x)` Queries
Search and insertion follow root-to-leaf paths, taking at most $O(\log n)$ comparisons:
```lean
theorem findSteps_le_log (c : ℕ) (t : BBST α)
    (hvh : t.ValidHeight) (hbal : t.IsHeightBalanced c) :
    findSteps t ≤ c * Nat.size t.size

def insertWork (n c : ℕ) : ℕ := c * Nat.size n + 2
theorem insertWork_le (n c : ℕ) : insertWork n c ≤ c * Nat.size n + 2
```
