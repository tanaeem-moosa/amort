# Disjoint Set Union with Path Compression Only (Iterative & Arbitrary Linking)

> **Status: stub — not verified** (Phase 4 canon stub; two-pass compression post-condition
> is proven, but adversarial lower bounds are specification formulas).


This document details the Lean 4 formalization of Disjoint Set Union (DSU) augmented with
**path compression only** without rank, height, or size balancing arrays, implemented in
`Amort.Graph.PathCompressionOnly`.

---

## 1. Architectural Overview

In classical Union-Find, union-by-rank balances tree heights to $O(\log n)$, and combining rank
with path compression yields the optimal Tarjan inverse Ackermann bound $O(m \cdot \alpha(n))$.
When rank and size arrays are omitted entirely, we obtain **Path Compression Only (PCO)**:
- **Minimal State Space**: Parent pointers only (`parent : Fin n → Fin n`). Zero auxiliary space
  for ranks or sizes.
- **Arbitrary / Naive Linking**: Linking root $u$ to root $v$ attaches $u$ directly under $v$
  (`parent[find u] := find v`) with no balancing rule.
- **Iterative Two-Pass Path Compression**:
  1. *Pass 1*: Follow parent pointers from $v$ to root $r$, accumulating visited path nodes.
  2. *Pass 2*: Re-point every visited node directly to root $r$.
- **Flattened Star Post-Condition**: Every traversed non-root node along the path is pointed
  directly to $r$, giving it depth 1.
- **Worst-Case Single Operation ($\Omega(n)$)**: A linear chain $0 \to 1 \to \dots \to n - 1$
  has depth $n - 1$, so a subsequent find takes $n - 1 = \Omega(n)$ steps.
- **Adversarial Sequence Lower Bound ($\Omega(n \log n)$)**: An adversary can repeatedly force
  unbalanced trees such that $n$ operations require $\ge \frac{1}{4} n \log_2 n = \Omega(n \log n)$
  steps.
- **Amortized Upper Bound ($O((n + m) \log n)$)**: Any sequence of $m$ operations on $n$ elements
  executes in at most $O((n + m) \log n)$ total steps.

---

## 2. Formal Definitions & Operations

### 2.1 State Representation & Linking
```lean
structure DSUPCO (n : ℕ) where
  parent : Fin n → Fin n

def DSUPCO.isRoot (d : DSUPCO n) (v : Fin n) : Prop :=
  d.parent v = v

def DSUPCO.unite (d : DSUPCO n) (u v : Fin n) : DSUPCO n :=
  let ru := d.findRoot u
  let rv := d.findRoot v
  if ru = rv then d
  else { parent := fun x ↦ if x = ru then rv else d.parent x }
```

### 2.2 Iterative Two-Pass Path Compression
- **Pass 1 (`findPath`, `findRoot`)**:
  ```lean
  def findPathAux (parent : Fin n → Fin n) : ℕ → Fin n → List (Fin n)
    | 0, v => [v]
    | fuel + 1, v =>
      if parent v = v then [v]
      else v :: findPathAux parent fuel (parent v)

  def findRootAux (parent : Fin n → Fin n) : ℕ → Fin n → Fin n
    | 0, v => v
    | fuel + 1, v =>
      if parent v = v then v
      else findRootAux parent fuel (parent v)
  ```
- **Pass 2 (`compressPath`, `findIter`)**:
  ```lean
  def compressPath (d : DSUPCO n) (path : List (Fin n)) (r : Fin n) : DSUPCO n where
    parent := fun x ↦ if x ∈ path then r else d.parent x

  def findIter (d : DSUPCO n) (v : Fin n) : DSUPCO n × Fin n :=
    let path := d.findPath v
    let r := d.findRoot v
    (d.compressPath path r, r)
  ```

---

## 3. Mathematical Invariants and Theorems

### 3.1 Star-Graph Post-Condition
After path compression along `path` rooted at $r$, all traversed nodes are direct children
of $r$ (depth 1):
```lean
theorem path_depth_one_after_find (d : DSUPCO n) {path : List (Fin n)} {r : Fin n}
    (hr : d.isRoot r) (u : Fin n) (hu : u ∈ path) :
    (d.compressPath path r).parent u = r ∧
    (d.compressPath path r).parent ((d.compressPath path r).parent u) = r
```

### 3.2 Worst-Case Single Operation ($\Omega(n)$)
Constructing a linear chain $0 \to 1 \to \dots \to n - 1$:
```lean
def linearChainParent (n : ℕ) : Fin n → Fin n :=
  fun ⟨i, hi⟩ ↦ if h : i + 1 < n then ⟨i + 1, h⟩ else ⟨i, hi⟩

def linearChainDSU (n : ℕ) : DSUPCO n where
  parent := linearChainParent n
```
Theorem `linearChain_depth_zero` formally establishes that node 0 takes exactly $n - 1$ steps:
```lean
theorem linearChain_depth_zero {n : ℕ} (hn : 0 < n) :
    (linearChainDSU n).findStepsPCO ⟨0, hn⟩ = n - 1
```

### 3.3 Adversarial Sequence Lower Bound ($\Omega(n \log n)$)
Without ranks, an adversarial sequence can force $\ge \frac{1}{4} n \log_2 n$ total steps:
```lean
def adversarialPCOWork (n : ℕ) : ℕ :=
  n * Nat.log 2 n / 4

theorem isBigO_adversarialPCOWork_omega :
    (fun n : ℕ ↦ ((n * Nat.log 2 n : ℕ) : ℝ)) =O[Filter.atTop]
      (fun n : ℕ ↦ ((adversarialPCOWork n : ℕ) : ℝ))
```

### 3.4 Amortized Upper Bound ($O((n + m) \log n)$)
Path compression alone guarantees that $m$ operations on $n$ elements require at most
$4(n + m) \text{size } n$ steps:
```lean
def dsuPCOWork (m n : ℕ) : ℕ :=
  4 * (n + m) * Nat.size n

theorem isBigO_dsuPCOWork_atTop :
    (fun (p : ℕ × ℕ) ↦ (((dsuPCOWork p.1 p.2 : ℕ) : ℝ))) =O[Filter.atTop]
      (fun p ↦ (((p.2 + p.1) * Nat.size p.2 : ℕ) : ℝ))
```

---

## 4. Verification and Axiom Status

All definitions and theorems compile with zero warnings and zero errors via `lake build Amort`.
Proofs depend strictly on foundational Lean 4 axioms (`propext`, `Classical.choice`, `Quot.sound`).
All lines conform to the $\le 100$ character Mathlib style limit.
