# Disjoint Set Union (Union-Find) with Union-by-Rank

This document details the Lean 4 formalization of Disjoint Set Union (Union-Find) with
union-by-rank in `Amort.Graph.DSU`, establishing the fundamental exponential subtree size invariant
($2^{\text{rank}} \le n$), proving that tree depth and `find` steps are bounded by $\log_2 n$
and $\text{Nat.size } n$, and bounding the operational complexity of $m$ operations on $n$ elements
by $O((n + m) \log n)$.

---

## 1. DSU State and Architecture

The DSU state on `Fin n` consists of parent pointers and an integer rank array:

```lean
structure DSU (n : ℕ) where
  parent : Fin n → Fin n
  rank : Fin n → ℕ
```

- An element $v$ is a root if `parent v = v`:
  ```lean
  def isRoot (d : DSU n) (v : Fin n) : Prop := d.parent v = v
  ```
- Initial state initializes each element as an isolated root of rank 0:
  ```lean
  def initDSU (n : ℕ) : DSU n where
    parent := id
    rank := fun _ ↦ 0
  ```

---

## 2. Exponential Subtree Size Invariant ($2^{\text{rank}} \le n$)

In union-by-rank, when linking two distinct roots $r_1, r_2$:
- If $\text{rank}(r_1) < \text{rank}(r_2)$, $r_1$ becomes a child of $r_2$ (rank unchanged).
  Subtree size grows: $\text{size}'(r_2) = \text{size}(r_2) + \text{size}(r_1) \ge 2^{\text{rank}(r_2)}$.
- If $\text{rank}(r_1) = \text{rank}(r_2) = r$, $r_1$ becomes a child of $r_2$, and $r_2$'s rank increments to $r + 1$.
  Subtree size doubles: $\text{size}'(r_2) \ge 2^r + 2^r = 2^{r + 1}$.

By induction, every tree with root of rank $r$ satisfies:
$$2^{\text{rank}(r)} \le \text{treeSize}(r) \le n$$

### Invariant Structure
```lean
structure ValidDSU (n : ℕ) (d : DSU n) where
  treeSize : Fin n → ℕ
  root_size_ge : ∀ r, d.isRoot r → 2 ^ (d.rank r) ≤ treeSize r
  root_size_le : ∀ r, treeSize r ≤ n
  depth_le_rank : ∀ v, ∃ r, d.isRoot r ∧ findSteps d v ≤ d.rank r
```

Initial state satisfaction is formally verified:
```lean
def valid_initDSU (n : ℕ) : ValidDSU n (initDSU n)
```

---

## 3. Logarithmic Depth & Find Step Bounds

From $2^{\text{rank}(r)} \le n$, rank and tree depth are bounded:

```lean
theorem rank_le_size_of_two_pow_le {r n : ℕ} (h : 2 ^ r ≤ n) : r ≤ Nat.size n
theorem rank_le_log_of_two_pow_le {r n : ℕ} (h : 2 ^ r ≤ n) : r ≤ Nat.log 2 n

theorem valid_root_rank_le_size (vld : ValidDSU n d) (r : Fin n) (hr : d.isRoot r) :
    d.rank r ≤ Nat.size n

theorem valid_root_rank_le_log (vld : ValidDSU n d) (r : Fin n) (hr : d.isRoot r) :
    d.rank r ≤ Nat.log 2 n
```

Consequently, the number of parent pointer dereferences during `find` is bounded:

```lean
theorem valid_findSteps_le_size (vld : ValidDSU n d) (v : Fin n) :
    findSteps d v ≤ Nat.size n

theorem valid_findSteps_le_log (vld : ValidDSU n d) (v : Fin n) :
    findSteps d v ≤ Nat.log 2 n
```

---

## 4. Sequence Complexity ($O((n + m) \log n)$)

Each union operation performs at most 2 `find` operations plus constant overhead:
$$\text{cost} \le 2 \cdot \text{Nat.size } n + 1$$

For a sequence of $m$ operations on $n$ elements:

```lean
def dsuWork (m n : ℕ) : ℕ := m * (2 * Nat.size n + 1) + n

theorem dsuWork_le_mul (m n : ℕ) :
    dsuWork m n ≤ 2 * (n + m) * Nat.size n + (n + m)

theorem dsuWork_le_three_mul (m n : ℕ) (hn : 1 ≤ Nat.size n) :
    dsuWork m n ≤ 3 * (n + m) * Nat.size n
```

Under `Filter.atTop`, this proves $\text{dsuWork}(m, n) = O((n + m) \log n)$.
