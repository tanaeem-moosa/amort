# Dynamic Array with Capacity Doubling

This document details the Lean 4 formalization of dynamic array capacity doubling via Tarjan's
potential method in `Amort.DataStructure.DynamicArray`. It proves that every push operation has
amortized cost $\hat{c} \le 3$ ($O(1)$) and that the total actual cost across $k$ pushes is bounded
by $3k + \Phi_0$.

---

## 1. State Model & Transition

A dynamic array state stores the current element count $n$ and allocated capacity $C$:

```lean
structure DynArrayState where
  size : ℕ
  capacity : ℕ
```

### State Transitions and Actual Costs
Upon `push`:
- If $n < C$, space is available. The actual operational cost is $c = 1$, and capacity is unchanged.
- If $n = C$, the array is full. Capacity doubles to $2C$, and all $n$ elements are copied over plus
  the new element is inserted. The actual operational cost is $c = n + 1$.

```lean
def pushState (s : DynArrayState) : DynArrayState :=
  if s.size < s.capacity then ⟨s.size + 1, s.capacity⟩
  else ⟨s.size + 1, 2 * s.capacity⟩

def pushActualCost (s : DynArrayState) : ℕ :=
  if s.size < s.capacity then 1
  else s.size + 1
```

---

## 2. Potential Method Analysis ($\Phi = 2n - C$)

We define the potential function:
$$\Phi(n, C) = 2n - C$$

```lean
def phi (s : DynArrayState) : ℤ :=
  2 * (s.size : ℤ) - (s.capacity : ℤ)
```

### Invariant Non-Negativity
Whenever the array is at least half full ($C \le 2n$):
$$\Phi(n, C) = 2n - C \ge 0$$
```lean
theorem phi_nonneg (s : DynArrayState) (h : s.capacity ≤ 2 * s.size) : 0 ≤ phi s
```

### Amortized Cost Derivation
The amortized cost $\hat{c}$ is defined as:
$$\hat{c} = c + \Phi(s') - \Phi(s)$$

We evaluate the two cases:
1. **Case 1: $n < C$ (No Doubling)**:
   - $c = 1$.
   - $n' = n + 1, C' = C$.
   - $\Delta \Phi = (2(n + 1) - C) - (2n - C) = 2$.
   - $\hat{c} = 1 + 2 = 3$.

2. **Case 2: $n = C$ (Doubling)**:
   - $c = n + 1 = C + 1$.
   - $n' = C + 1, C' = 2C$.
   - $\Phi' = 2(C + 1) - 2C = 2$.
   - $\Phi = 2C - C = C$.
   - $\Delta \Phi = 2 - C$.
   - $\hat{c} = (C + 1) + (2 - C) = 3$.

Milestone theorems prove this equality and bound:
```lean
theorem pushAmortizedCost_eq_three (s : DynArrayState) (hle : s.size ≤ s.capacity) :
    pushAmortizedCost s = 3

theorem pushAmortizedCost_le_three (s : DynArrayState) (hle : s.size ≤ s.capacity) :
    pushAmortizedCost s ≤ 3
```

---

## 3. Multi-Operation Telescoping

For any sequence of $k$ pushes, summing the amortized costs yields:
$$\sum_{i=1}^k c_i = \sum_{i=1}^k \hat{c}_i - (\Phi_k - \Phi_0) = 3k - \Phi_k + \Phi_0$$

Milestone theorems:
```lean
theorem pushSeqCost_telescope (k : ℕ) (s : DynArrayState)
    (hle : ∀ j < k, (pushSeq j s).size ≤ (pushSeq j s).capacity) :
    (pushSeqCost k s : ℤ) = 3 * (k : ℤ) - phi (pushSeq k s) + phi s

theorem pushSeqCost_le_three_mul_add (k : ℕ) (s : DynArrayState)
    (hle : ∀ j < k, (pushSeq j s).size ≤ (pushSeq j s).capacity)
    (hphi : 0 ≤ phi (pushSeq k s)) :
    (pushSeqCost k s : ℤ) ≤ 3 * (k : ℤ) + phi s
```
