/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Two-Stack FIFO Queue with Amortized O(1) Operations

This module formalizes the classic two-stack FIFO queue and its amortized complexity analysis
via the potential method:
- Representation: two stacks `inStack` and `outStack` of type `List α`.
- Logical FIFO contents: `toList q = q.outStack ++ q.inStack.reverse`.
- Potential function: $\Phi(q) = 2 \cdot |\text{inStack}|$.
- Operational costs:
  - Push (enqueue): cost 1, $\Delta \Phi = 2$, amortized cost $\hat{c} = 1 + 2 = 3$.
  - Pop (dequeue):
    - if `outStack` non-empty: cost 1, $\Delta \Phi = 0$, amortized cost $\hat{c} = 1 \le 3$.
    - if `outStack` empty and `inStack` non-empty: cost $|\text{inStack}| + 1$,
      $\Delta \Phi = -2 \cdot |\text{inStack}|$, amortized cost
      $\hat{c} = (|\text{inStack}| + 1) - 2 |\text{inStack}| = 1 - |\text{inStack}| \le 1 \le 3$.
    - if both empty: cost 0, $\Delta \Phi = 0$, amortized cost 0.
- Sequence bound: across any sequence of $m$ operations starting from an empty queue,
  the total actual operational cost is bounded by $3m$.

## Mathematical Architecture

1. **Queue Structure & FIFO Correctness**:
   - `TwoStackQueue α`: pair of lists `(inStack, outStack)`.
   - `toList q = q.outStack ++ q.inStack.reverse`.
   - `toList_push`: pushing $x$ appends $x$ to the end of the logical queue.
   - `pop_spec`: popping extracts the head of `toList q`.

2. **Potential Method (Tarjan)**:
   - `phi q = 2 * q.inStack.length`.
   - `pushAmortizedCost q x = 3`.
   - `popAmortizedCost q ≤ 1`.
   - In all cases, every operation has amortized cost $\le 3$.

3. **Multi-Operation Telescoping**:
   - `QueueOp α`: inductive datatype representing push or pop operations.
   - `totalActualCost ops q`: sum of actual work executed across the sequence `ops`.
   - Milestone Theorem: `totalActualCost_le_three_mul` proves
     $\sum c_i \le 3 \cdot |\text{ops}| + \Phi(q_0)$.

## Key Definitions and Theorems
- `Amort.DataStructure.TwoStackQueue`: Structure holding `inStack` and `outStack`.
- `Amort.DataStructure.TwoStackQueue.toList`: Logical FIFO representation.
- `Amort.DataStructure.TwoStackQueue.toList_push`: FIFO append preservation.
- `Amort.DataStructure.TwoStackQueue.phi`: Potential function $\Phi = 2 \cdot |\text{inStack}|$.
- `Amort.DataStructure.TwoStackQueue.pushAmortizedCost_eq_three`: Exact amortized push cost = 3.
- `Amort.DataStructure.TwoStackQueue.popAmortizedCost_le_one`: Amortized pop cost $\le 1$.
- `Amort.DataStructure.TwoStackQueue.popAmortizedCost_le_three`: Amortized pop bound $\le 3$.
- `Amort.DataStructure.totalActualCost_le_three_mul`: Telescoping total actual cost bound.
-/

namespace Amort.DataStructure

/-- Two-stack FIFO queue backed by an input stack and an output stack. -/
structure TwoStackQueue (α : Type*) where
  inStack : List α
  outStack : List α
  deriving Repr, DecidableEq

namespace TwoStackQueue

/-- Initial empty queue with both stacks empty. -/
def empty {α : Type*} : TwoStackQueue α :=
  ⟨[], []⟩

/-- Logical FIFO element sequence: elements in `outStack` followed by
reversed elements of `inStack`. -/
def toList {α : Type*} (q : TwoStackQueue α) : List α :=
  q.outStack ++ q.inStack.reverse

@[simp]
theorem toList_empty {α : Type*} : (empty : TwoStackQueue α).toList = [] := rfl

/-- Total number of elements in the queue. -/
def size {α : Type*} (q : TwoStackQueue α) : ℕ :=
  q.inStack.length + q.outStack.length

theorem length_toList {α : Type*} (q : TwoStackQueue α) :
    q.toList.length = q.size := by
  dsimp [toList, size]
  simp only [List.length_append, List.length_reverse]
  omega

/-- Potential function for amortized analysis: $\Phi(q) = 2 \cdot |\text{inStack}|$. -/
def phi {α : Type*} (q : TwoStackQueue α) : ℕ :=
  2 * q.inStack.length

@[simp]
theorem phi_empty {α : Type*} : (empty : TwoStackQueue α).phi = 0 := rfl

/-- Push (enqueue) operation: conses the element onto `inStack`. -/
def push {α : Type*} (q : TwoStackQueue α) (x : α) : TwoStackQueue α :=
  ⟨x :: q.inStack, q.outStack⟩

/-- FIFO Soundness: pushing an element $x$ appends $x$ to the logical queue. -/
theorem toList_push {α : Type*} (q : TwoStackQueue α) (x : α) :
    (q.push x).toList = q.toList ++ [x] := by
  dsimp [push, toList]
  simp only [List.reverse_cons, List.append_assoc]

/-- Pop (dequeue) operation:
if `outStack` is non-empty, pops its head;
if `outStack` is empty, reverses `inStack` into `outStack` and pops its head. -/
def pop {α : Type*} (q : TwoStackQueue α) : Option α × TwoStackQueue α :=
  match q.outStack with
  | x :: xs => (some x, ⟨q.inStack, xs⟩)
  | [] =>
    match q.inStack.reverse with
    | [] => (none, ⟨[], []⟩)
    | x :: xs => (some x, ⟨[], xs⟩)

/-- Popping extracts the head element of the logical FIFO queue. -/
theorem pop_fst {α : Type*} (q : TwoStackQueue α) :
    (q.pop).1 = q.toList.head? := by
  dsimp [pop, toList]
  cases q.outStack with
  | cons x xs => rfl
  | nil =>
    cases h : q.inStack.reverse with
    | nil => rfl
    | cons x xs => rfl

/-- Popping produces a queue whose logical contents are the tail of the original queue. -/
theorem pop_snd_toList {α : Type*} (q : TwoStackQueue α) :
    (q.pop).2.toList = q.toList.tail := by
  dsimp [pop, toList]
  cases q.outStack with
  | cons x xs => rfl
  | nil =>
    dsimp
    cases h : q.inStack.reverse with
    | nil => rfl
    | cons x xs =>
      dsimp [toList]
      rw [List.append_nil]

/-- Full FIFO specification of pop: extracting the head element and transitioning to the tail. -/
theorem pop_spec {α : Type*} (q : TwoStackQueue α) :
    (q.pop).1 = q.toList.head? ∧ (q.pop).2.toList = q.toList.tail :=
  ⟨pop_fst q, pop_snd_toList q⟩

/-- Actual operational cost of push is 1 unit. -/
def pushActualCost {α : Type*} (_q : TwoStackQueue α) : ℕ := 1

/-- Actual operational cost of pop:
1 unit if `outStack` non-empty,
$|\text{inStack}| + 1$ units if `inStack` reversed into `outStack`,
0 units if queue is already empty. -/
def popActualCost {α : Type*} (q : TwoStackQueue α) : ℕ :=
  match q.outStack, q.inStack with
  | _ :: _, _ => 1
  | [], _ :: _ => q.inStack.length + 1
  | [], [] => 0

/-- Amortized cost of push via the potential method:
$\hat{c} = c + \Phi(q') - \Phi(q) = 1 + 2(n + 1) - 2n = 3$. -/
def pushAmortizedCost {α : Type*} (q : TwoStackQueue α) (x : α) : ℤ :=
  (pushActualCost q : ℤ) + ((q.push x).phi : ℤ) - (q.phi : ℤ)

/-- Milestone Theorem: amortized cost of push is identically 3. -/
theorem pushAmortizedCost_eq_three {α : Type*} (q : TwoStackQueue α) (x : α) :
    pushAmortizedCost q x = 3 := by
  dsimp [pushAmortizedCost, pushActualCost, push, phi]
  omega

/-- Milestone Bound: amortized cost of push is bounded by 3 ($T_{\text{amortized}} \le 3$). -/
theorem pushAmortizedCost_le_three {α : Type*} (q : TwoStackQueue α) (x : α) :
    pushAmortizedCost q x ≤ 3 := by
  rw [pushAmortizedCost_eq_three]

/-- Amortized cost of pop via the potential method:
$\hat{c} = c + \Phi(q') - \Phi(q)$. -/
def popAmortizedCost {α : Type*} (q : TwoStackQueue α) : ℤ :=
  let res := q.pop
  (popActualCost q : ℤ) + (res.2.phi : ℤ) - (q.phi : ℤ)

/-- Milestone Theorem: amortized cost of pop is bounded by 1. -/
theorem popAmortizedCost_le_one {α : Type*} (q : TwoStackQueue α) :
    popAmortizedCost q ≤ 1 := by
  dsimp [popAmortizedCost, popActualCost, pop, phi]
  cases q.outStack with
  | cons x xs =>
    dsimp
    omega
  | nil =>
    dsimp
    cases h_in : q.inStack with
    | nil =>
      dsimp
      omega
    | cons y ys =>
      dsimp
      cases h_rev : (y :: ys).reverse with
      | nil =>
        have : (y :: ys).reverse ≠ [] := by simp
        contradiction
      | cons z zs =>
        dsimp
        omega

/-- Milestone Bound: amortized cost of pop is bounded by 3 ($T_{\text{amortized}} \le 3$). -/
theorem popAmortizedCost_le_three {α : Type*} (q : TwoStackQueue α) :
    popAmortizedCost q ≤ 3 := by
  have := popAmortizedCost_le_one q
  omega

end TwoStackQueue

/-! ### Multi-Operation Sequences & Telescoping Bounds -/

/-- Queue operation: either pushing an element or popping. -/
inductive QueueOp (α : Type*) where
  | push (x : α) : QueueOp α
  | pop : QueueOp α
  deriving Repr, DecidableEq

/-- State transition under a single queue operation. -/
def applyOp {α : Type*} (op : QueueOp α) (q : TwoStackQueue α) : TwoStackQueue α :=
  match op with
  | .push x => q.push x
  | .pop => (q.pop).2

/-- Actual operational cost of a single queue operation. -/
def opActualCost {α : Type*} (op : QueueOp α) (q : TwoStackQueue α) : ℕ :=
  match op with
  | .push _ => TwoStackQueue.pushActualCost q
  | .pop => TwoStackQueue.popActualCost q

/-- Amortized cost of a single queue operation. -/
def opAmortizedCost {α : Type*} (op : QueueOp α) (q : TwoStackQueue α) : ℤ :=
  (opActualCost op q : ℤ) + ((applyOp op q).phi : ℤ) - (q.phi : ℤ)

/-- Amortized cost of every operation is bounded by 3. -/
theorem opAmortizedCost_le_three {α : Type*} (op : QueueOp α) (q : TwoStackQueue α) :
    opAmortizedCost op q ≤ 3 := by
  cases op with
  | push x =>
    dsimp [opAmortizedCost, opActualCost, applyOp]
    exact TwoStackQueue.pushAmortizedCost_le_three q x
  | pop =>
    dsimp [opAmortizedCost, opActualCost, applyOp]
    exact TwoStackQueue.popAmortizedCost_le_three q

/-- Cumulative state after executing a list of operations. -/
def execOps {α : Type*} : List (QueueOp α) → TwoStackQueue α → TwoStackQueue α
  | [], q => q
  | op :: ops, q => execOps ops (applyOp op q)

/-- Cumulative actual cost across a list of operations. -/
def totalActualCost {α : Type*} : List (QueueOp α) → TwoStackQueue α → ℕ
  | [], _ => 0
  | op :: ops, q => opActualCost op q + totalActualCost ops (applyOp op q)

/-- Telescoping theorem for Two-Stack Queue: cumulative actual cost across any sequence
of operations is bounded by $3 \cdot |\text{ops}| + \Phi(q_0)$. -/
theorem totalActualCost_le_three_mul {α : Type*} (ops : List (QueueOp α))
    (q : TwoStackQueue α) :
    (totalActualCost ops q : ℤ) ≤ 3 * (ops.length : ℤ) + (q.phi : ℤ) := by
  induction ops generalizing q with
  | nil =>
    dsimp [totalActualCost]
    omega
  | cons op ops ih =>
    dsimp [totalActualCost, List.length]
    have h_op := opAmortizedCost_le_three op q
    dsimp [opAmortizedCost] at h_op
    have h_rest := ih (applyOp op q)
    linarith

/-- Milestone Corollary: starting from an empty queue ($\Phi = 0$), the total actual
cost of $m$ operations is bounded by $3m$. -/
theorem totalActualCost_empty_le {α : Type*} (ops : List (QueueOp α)) :
    totalActualCost ops TwoStackQueue.empty ≤ 3 * ops.length := by
  have h := totalActualCost_le_three_mul ops (TwoStackQueue.empty : TwoStackQueue α)
  dsimp [TwoStackQueue.phi] at h
  omega

end Amort.DataStructure
