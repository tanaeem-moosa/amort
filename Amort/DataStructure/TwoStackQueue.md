# Two-Stack FIFO Queue with Amortized O(1) Operations

This document details the Lean 4 formalization of the two-stack FIFO queue in
`Amort.DataStructure.TwoStackQueue`, establishing FIFO queue soundness, potential function
analysis ($\Phi = 2 \cdot |\text{inStack}|$), and bounding the total operational work across
$m$ operations by $3m$.

---

## 1. Queue State & Logical Representation

The queue is represented by an input stack and an output stack:

```lean
structure TwoStackQueue (α : Type*) where
  inStack : List α
  outStack : List α
```

### Logical FIFO Sequence
The sequence of elements in FIFO order is formed by elements in `outStack` followed by elements
in `inStack` reversed:
```lean
def toList (q : TwoStackQueue α) : List α :=
  q.outStack ++ q.inStack.reverse
```

Milestone theorem `toList_push` establishes FIFO append soundness:
```lean
theorem toList_push (q : TwoStackQueue α) (x : α) :
    (q.push x).toList = q.toList ++ [x]
```

---

## 2. Potential Method Analysis ($\Phi = 2 \cdot |\text{inStack}|$)

The potential function counts twice the number of elements residing in `inStack`:
```lean
def phi (q : TwoStackQueue α) : ℕ := 2 * q.inStack.length
```

Because natural numbers are non-negative, $\Phi(q) \ge 0$ unconditionally, with $\Phi(\text{empty})
= 0$.

### Amortized Cost of Push ($\hat{c} = 3$)
- Actual cost: $c = 1$.
- New state: `x :: inStack`, so $|\text{inStack}'| = |\text{inStack}| + 1$.
- $\Delta \Phi = 2(|\text{inStack}| + 1) - 2|\text{inStack}| = 2$.
- $\hat{c} = 1 + 2 = 3$.

```lean
theorem pushAmortizedCost_eq_three (q : TwoStackQueue α) (x : α) :
    pushAmortizedCost q x = 3
```

### Amortized Cost of Pop ($\hat{c} \le 1 \le 3$)
- **Case 1: `outStack` non-empty**:
  $c = 1$. `inStack` is unchanged, so $\Delta \Phi = 0$.
  $\hat{c} = 1 + 0 = 1 \le 3$.
- **Case 2: `outStack` empty, `inStack` non-empty**:
  All $n$ elements in `inStack` are reversed into `outStack` at cost $n$, and 1 element is popped,
  giving actual cost $c = n + 1$.
  `inStack` becomes empty, so $\Phi' = 0$.
  $\Delta \Phi = 0 - 2n = -2n$.
  $\hat{c} = (n + 1) - 2n = 1 - n \le 1 \le 3$.
- **Case 3: both empty**:
  $c = 0$, $\Delta \Phi = 0$, $\hat{c} = 0 \le 3$.

```lean
theorem popAmortizedCost_le_one (q : TwoStackQueue α) : popAmortizedCost q ≤ 1
theorem popAmortizedCost_le_three (q : TwoStackQueue α) : popAmortizedCost q ≤ 3
```

---

## 3. Sequence Complexity & Telescoping Bound

For any sequence of $m$ operations (`push` and `pop`) applied to an initially empty queue:
$$\sum_{i=1}^m c_i = \sum_{i=1}^m \hat{c}_i - (\Phi_m - \Phi_0) \le 3m - \Phi_m + 0 \le 3m$$

Milestone theorems:
```lean
theorem totalActualCost_le_three_mul (ops : List (QueueOp α)) (q : TwoStackQueue α) :
    (totalActualCost ops q : ℤ) ≤ 3 * (ops.length : ℤ) + (q.phi : ℤ)

theorem totalActualCost_empty_le (ops : List (QueueOp α)) :
    totalActualCost ops TwoStackQueue.empty ≤ 3 * ops.length
```
