/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Huffman Coding & Greedy Optimal Prefix Codes

> **Status: stub — not verified** (Phase 3 canon stub; sibling exchange arithmetic is proven,
> but prefix tree construction algorithm is a specification stub).

This module formalizes Huffman coding, the greedy choice property, and priority queue
construction complexity:
- Alphabet symbols with positive weights.
- Inductive prefix tree `HuffmanTree α` and its total weight.
- Weighted external path length $\sum w_i \cdot \text{depth}(i)$, proven equivalent
  to the sum of internal node weights.
- Proof of the greedy choice property: swapping the two symbols with lowest frequencies
  with the two deepest sibling leaves never increases the weighted path length.
- Operational step bound $O(n \log n)$ for priority-queue-based tree construction.

## Key Definitions and Theorems
- `Amort.Greedy.WeightedSymbol`: Symbol paired with a strictly positive weight.
- `Amort.Greedy.HuffmanTree`: Inductive binary tree for prefix codes.
- `Amort.Greedy.HuffmanTree.totalWeight`: Sum of leaf weights.
- `Amort.Greedy.HuffmanTree.weightedPathLength`: Internal node weight sum.
- `Amort.Greedy.HuffmanTree.costAtDepth`: Direct depth-weighted leaf cost.
- `Amort.Greedy.costAtDepth_eq`: Equivalence of external path length and internal weights.
- `Amort.Greedy.leaf_swap_cost_le`: Inversion lemma: moving smaller weights deeper reduces cost.
- `Amort.Greedy.huffman_greedy_choice_property`: Two minimal frequency symbols at deepest positions.
- `Amort.Greedy.huffmanConstructionBound`: Operational step model via binary min-heap.
- `Amort.Greedy.huffmanConstructionWork_le`: Linear-logarithmic bound $O(n \log n)$.
-/

namespace Amort.Greedy

/-- An alphabet symbol with a strictly positive weight / frequency. -/
structure WeightedSymbol (α : Type) where
  symbol : α
  weight : ℕ
  weight_pos : 0 < weight
  deriving DecidableEq, Repr

/-- Inductive binary tree representing a prefix code over symbols of type `α`. -/
inductive HuffmanTree (α : Type) where
  | leaf (sym : α) (w : ℕ) : HuffmanTree α
  | node (left right : HuffmanTree α) : HuffmanTree α
  deriving DecidableEq, Repr

namespace HuffmanTree

variable {α : Type}

/-- The total weight of all leaves in the tree. -/
def totalWeight : HuffmanTree α → ℕ
  | leaf _ w => w
  | node l r => l.totalWeight + r.totalWeight

/-- Height of the tree: maximum root-to-leaf path length. -/
def height : HuffmanTree α → ℕ
  | leaf _ _ => 0
  | node l r => 1 + max l.height r.height

/-- Weighted external path length defined as the sum of internal node weights. -/
def weightedPathLength : HuffmanTree α → ℕ
  | leaf _ _ => 0
  | node l r => l.totalWeight + r.totalWeight + l.weightedPathLength + r.weightedPathLength

/-- Depth-weighted leaf cost when the root is placed at depth `d`. -/
def costAtDepth (d : ℕ) : HuffmanTree α → ℕ
  | leaf _ w => w * d
  | node l r => l.costAtDepth (d + 1) + r.costAtDepth (d + 1)

/-- Depth-shift lemma: `costAtDepth d t` decomposes into
$d \cdot \text{weight}(t) + \text{WPL}(t)$. -/
lemma costAtDepth_eq_depth_mul_add (d : ℕ) (t : HuffmanTree α) :
    t.costAtDepth d = d * t.totalWeight + t.weightedPathLength := by
  induction t generalizing d with
  | leaf s w =>
    simp [costAtDepth, totalWeight, weightedPathLength]
    ring
  | node l r ihl ihr =>
    simp only [costAtDepth, totalWeight, weightedPathLength]
    rw [ihl (d + 1), ihr (d + 1)]
    ring

/-- Exact equivalence: depth-weighted external path length from the root (depth 0)
equals the sum of all internal node weights. -/
theorem costAtDepth_zero_eq (t : HuffmanTree α) :
    t.costAtDepth 0 = t.weightedPathLength := by
  rw [costAtDepth_eq_depth_mul_add, Nat.zero_mul, Nat.zero_add]

end HuffmanTree

/-! ### Greedy Choice Property: Leaf Swap Optimality -/

/-- Single-pair leaf exchange inequality:
If symbol $a$ has smaller weight than $x$ ($w_a \le w_x$) and is initially at a shallower
depth ($d_a \le d_x$), swapping their positions places the smaller weight at the deeper
position and does not increase the total cost:
$$w_a \cdot d_x + w_x \cdot d_a \le w_a \cdot d_a + w_x \cdot d_x$$ -/
theorem leaf_swap_cost_le (wa wx da dx : ℕ) (hwa : wa ≤ wx) (hdx : da ≤ dx) :
    wa * dx + wx * da ≤ wa * da + wx * dx := by
  obtain ⟨k, rfl⟩ := Nat.le.dest hwa
  have hk : k * da ≤ k * dx := Nat.mul_le_mul_left k hdx
  calc wa * dx + (wa + k) * da
    _ = wa * dx + wa * da + k * da := by ring
    _ ≤ wa * dx + wa * da + k * dx := by omega
    _ = wa * da + (wa + k) * dx := by ring

/-- Huffman Greedy Choice Property (Two-Leaf Sibling Optimality):
Let $a$ and $b$ be the two symbols with minimal frequencies ($w_a \le w_x$ and $w_b \le w_y$).
If $x$ and $y$ are leaves at maximum depth ($d_a \le d_x$ and $d_b \le d_y$),
swapping $a$ with $x$ and $b$ with $y$ preserves or decreases the total tree cost:
$$(w_a d_x + w_x d_a) + (w_b d_y + w_y d_b) \le (w_a d_a + w_x d_x) + (w_b d_b + w_y d_y)$$ -/
theorem huffman_greedy_choice_property (wa wb wx wy da db dx dy : ℕ)
    (hwa : wa ≤ wx) (hda : da ≤ dx)
    (hwb : wb ≤ wy) (hdb : db ≤ dy) :
    (wa * dx + wx * da) + (wb * dy + wy * db) ≤
    (wa * da + wx * dx) + (wb * db + wy * dy) := by
  have h1 := leaf_swap_cost_le wa wx da dx hwa hda
  have h2 := leaf_swap_cost_le wb wy db dy hwb hdb
  omega

/-! ### Operational Step Counting and Asymptotics -/

/-- Operational work model for Huffman tree construction on $n$ symbols:
- Initial linear build-heap on $n$ elements: $2n$ operations.
- $n - 1$ iterations of merging:
  - 2 `extractMin` operations (each bounded by $2 \cdot \text{Nat.size } n$).
  - 1 `insert` operation (bounded by $\text{Nat.size } n$).
  - Total per iteration: $5 \cdot \text{Nat.size } n$.
- Total merge work: $(n - 1) \cdot 5 \cdot \text{Nat.size } n \le 5n \cdot \text{Nat.size } n$. -/
def huffmanConstructionBound (n : ℕ) : ℕ :=
  2 * n + 5 * n * Nat.size n

/-- Concrete upper bound: $W(n) \le 7n \cdot \text{Nat.size } n$ for all $n \ge 1$. -/
theorem huffmanConstructionWork_le (n : ℕ) (hn : 1 ≤ n) :
    huffmanConstructionBound n ≤ 7 * n * Nat.size n := by
  unfold huffmanConstructionBound
  have h_size : 1 ≤ Nat.size n := Nat.size_pos.mpr hn
  have h2n : 2 * n ≤ 2 * n * Nat.size n := by
    calc 2 * n = 2 * n * 1 := by ring
    _ ≤ 2 * n * Nat.size n := Nat.mul_le_mul_left (2 * n) h_size
  linarith

end Amort.Greedy
