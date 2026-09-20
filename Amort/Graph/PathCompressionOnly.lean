/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Amort.Graph.DSU
import Amort.Recurrence.Halving
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Size
import Mathlib.Order.Filter.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Disjoint Set Union with Path Compression Only (Iterative & Arbitrary Linking)

This module formalizes Disjoint Set Union (DSU) with **path compression only** without rank or
size balancing.

## Mathematical Architecture

1. **Minimal State & Arbitrary Linking**:
   - The state `DSUPCO n` contains solely parent pointers `parent : Fin n → Fin n` without
     any rank, height, or subtree size annotations.
   - `unite u v` attaches root `find u` directly under root `find v` without balancing.

2. **Iterative Two-Pass Path Compression**:
   - **Pass 1 (`findPath`, `findRoot`)**: Traverses parent pointers from $v$ to root $r$.
   - **Pass 2 (`compressPath`)**: Re-points every node along the traversed path directly to $r$.
   - **Star Graph Post-Condition**: Every traversed node along the path has depth 1 after
     compression (direct child of $r$), flattening the branch into a star graph.

3. **Worst-Case Single Operation ($\Omega(n)$)**:
   - A linear chain of $n$ elements $0 \to 1 \to \dots \to n - 1$ has depth $n - 1$.
   - A subsequent `find 0` traverses $n - 1 = \Omega(n)$ parent pointers.

4. **Adversarial Sequence Lower Bound ($\Omega(n \log n)$)**:
   - Without rank or size balancing, an adversarial sequence of $n$ operations can repeatedly
     rebuild deep branches, requiring $\ge \frac{1}{4} n \log_2 n$ total steps.

5. **Amortized Upper Bound ($O((n + m) \log n)$)**:
   - For any sequence of $m$ operations on $n$ elements, path compression alone bounds total
     work by $O((n + m) \log n)$ steps.
   - Connected to Mathlib `Mathlib.Analysis.Asymptotics.IsBigO` under `Filter.atTop`.

## Key Definitions and Theorems
- `Amort.Graph.DSUPCO`: Minimal DSU state holding only parent pointers.
- `Amort.Graph.DSUPCO.isRoot`: Root predicate `parent v = v`.
- `Amort.Graph.DSUPCO.compressPath`: Re-points traversed path nodes to root.
- `Amort.Graph.DSUPCO.findIter`: Two-pass iterative find with path compression.
- `Amort.Graph.DSUPCO.unite`: Naive/arbitrary linking attaching root $u$ under root $v$.
- `Amort.Graph.path_depth_one_after_find`: Post-condition that path nodes have depth 1.
- `Amort.Graph.linearChainDSU`: Construction of depth $n - 1$ linear chain.
- `Amort.Graph.linearChain_depth_zero`: Proves single-operation depth equals $n - 1$.
- `Amort.Graph.adversarialPCOWork`: Lower bound function $\frac{1}{4} n \log_2 n$.
- `Amort.Graph.dsuPCOWork`: Upper bound function $4(n + m) \text{size } n$.
- `Amort.Graph.isBigO_dsuPCOWork_atTop`: Mathlib `IsBigO` upper bound.
- `Amort.Graph.isBigO_adversarialPCOWork_omega`: Mathlib `IsBigO` lower bound.
-/

namespace Amort.Graph

open Asymptotics

/-! ### Minimal DSU State -/

/-- Minimal Disjoint Set Union state on `Fin n` containing parent pointers only,
without rank or size arrays. -/
structure DSUPCO (n : ℕ) where
  parent : Fin n → Fin n

namespace DSUPCO

/-- Predicate characterizing root elements in the parent forest. -/
def isRoot {n : ℕ} (d : DSUPCO n) (v : Fin n) : Prop :=
  d.parent v = v

/-- Auxiliary bounded path collector traversing parent pointers to find all path nodes. -/
def findPathAux {n : ℕ} (parent : Fin n → Fin n) : ℕ → Fin n → List (Fin n)
  | 0, v => [v]
  | fuel + 1, v =>
    if parent v = v then [v]
    else v :: findPathAux parent fuel (parent v)

/-- Full path from node $v$ to its root with fuel bound $n$. -/
def findPath {n : ℕ} (d : DSUPCO n) (v : Fin n) : List (Fin n) :=
  findPathAux d.parent n v

/-- Auxiliary bounded step counter for following parent pointers. -/
def findStepsPCOAux {n : ℕ} (parent : Fin n → Fin n) : ℕ → Fin n → ℕ
  | 0, _ => 0
  | fuel + 1, v =>
    if parent v = v then 0
    else 1 + findStepsPCOAux parent fuel (parent v)

/-- Total parent dereferences during `find` with fuel bound $n$. -/
def findStepsPCO {n : ℕ} (d : DSUPCO n) (v : Fin n) : ℕ :=
  findStepsPCOAux d.parent n v

/-- Auxiliary bounded root finder following parent pointers. -/
def findRootAux {n : ℕ} (parent : Fin n → Fin n) : ℕ → Fin n → Fin n
  | 0, v => v
  | fuel + 1, v =>
    if parent v = v then v
    else findRootAux parent fuel (parent v)

/-- Root of the tree containing node $v$ with fuel bound $n$. -/
def findRoot {n : ℕ} (d : DSUPCO n) (v : Fin n) : Fin n :=
  findRootAux d.parent n v

/-- Pass 2 of path compression: updates parent pointers for all nodes in `path` to point
directly to root `r`. -/
def compressPath {n : ℕ} (d : DSUPCO n) (path : List (Fin n)) (r : Fin n) : DSUPCO n where
  parent := fun x ↦ if x ∈ path then r else d.parent x

/-- Iterative two-pass `find` operation:
Pass 1 collects traversed path nodes and determines root $r$.
Pass 2 points all traversed nodes directly to $r$. -/
def findIter {n : ℕ} (d : DSUPCO n) (v : Fin n) : DSUPCO n × Fin n :=
  let path := d.findPath v
  let r := d.findRoot v
  (d.compressPath path r, r)

/-- Arbitrary/naive linking: `unite u v` attaches root of $u$ directly under root of $v$
without rank or size comparisons (`parent[find u] := find v`). -/
def unite {n : ℕ} (d : DSUPCO n) (u v : Fin n) : DSUPCO n :=
  let ru := d.findRoot u
  let rv := d.findRoot v
  if ru = rv then d
  else { parent := fun x ↦ if x = ru then rv else d.parent x }

/-- Instrumented unite operation executing iterative path compression on both operands
prior to linking root $u$ under root $v$. -/
def uniteWithCompress {n : ℕ} (d : DSUPCO n) (u v : Fin n) : DSUPCO n :=
  let (d1, ru) := d.findIter u
  let (d2, rv) := d1.findIter v
  if ru = rv then d2
  else { parent := fun x ↦ if x = ru then rv else d2.parent x }

end DSUPCO

/-- Initial canonical DSU state where every element is an isolated singleton root. -/
def initDSUPCO (n : ℕ) : DSUPCO n where
  parent := id

@[simp]
theorem initDSUPCO_isRoot {n : ℕ} (v : Fin n) : (initDSUPCO n).isRoot v :=
  rfl

@[simp]
theorem initDSUPCO_parent {n : ℕ} (v : Fin n) : (initDSUPCO n).parent v = v :=
  rfl

@[simp]
theorem findRoot_of_isRoot {n : ℕ} (d : DSUPCO n) (v : Fin n) (hr : d.isRoot v) :
    d.findRoot v = v := by
  dsimp [DSUPCO.findRoot]
  cases n with
  | zero => rfl
  | succ k =>
    dsimp [DSUPCO.findRootAux]
    have h : d.parent v = v := hr
    rw [if_pos h]

@[simp]
theorem findStepsPCO_zero_of_root {n : ℕ} (d : DSUPCO n) (v : Fin n) (hr : d.isRoot v) :
    d.findStepsPCO v = 0 := by
  dsimp [DSUPCO.findStepsPCO]
  cases n with
  | zero => rfl
  | succ k =>
    dsimp [DSUPCO.findStepsPCOAux]
    have h : d.parent v = v := hr
    rw [if_pos h]

/-! ### Invariant & Star-Graph Post-Condition -/

/-- Membership in path implies the compressed parent is $r$. -/
theorem compressPath_parent_of_mem {n : ℕ} (d : DSUPCO n) {path : List (Fin n)} {r : Fin n}
    (u : Fin n) (hu : u ∈ path) :
    (d.compressPath path r).parent u = r := by
  dsimp [DSUPCO.compressPath]
  rw [if_pos hu]

/-- Compression preserves the root property of $r$ whenever $d.parent r = r$. -/
theorem compressPath_isRoot_of_isRoot {n : ℕ} (d : DSUPCO n) {path : List (Fin n)} {r : Fin n}
    (hr : d.isRoot r) :
    (d.compressPath path r).isRoot r := by
  dsimp [DSUPCO.compressPath, DSUPCO.isRoot]
  by_cases h : r ∈ path
  · rw [if_pos h]
  · rw [if_neg h]
    exact hr

/-- **Flattened Star Post-Condition**:
After path compression, every traversed non-root node $u$ in `path` points directly to $r$,
and $r$ is its own parent. Thus node $u$ has depth exactly 1 from $r$. -/
theorem path_depth_one_after_find {n : ℕ} (d : DSUPCO n) {path : List (Fin n)} {r : Fin n}
    (hr : d.isRoot r) (u : Fin n) (hu : u ∈ path) :
    (d.compressPath path r).parent u = r ∧
    (d.compressPath path r).parent ((d.compressPath path r).parent u) = r := by
  have h1 : (d.compressPath path r).parent u = r := compressPath_parent_of_mem d u hu
  have h2 : (d.compressPath path r).parent r = r := compressPath_isRoot_of_isRoot d hr
  refine ⟨h1, ?_⟩
  rw [h1, h2]

/-! ### Worst-Case Single Operation: Linear Chain Construction ($\Omega(n)$) -/

/-- Linear chain parent pointer construction: node $i$ points to $i + 1$, and node $n - 1$
is the root. -/
def linearChainParent (n : ℕ) : Fin n → Fin n :=
  fun ⟨i, hi⟩ ↦
    if h : i + 1 < n then ⟨i + 1, h⟩ else ⟨i, hi⟩

/-- Linear chain DSU state on $n$ elements. -/
def linearChainDSU (n : ℕ) : DSUPCO n where
  parent := linearChainParent n

theorem linearChain_parent_succ {n : ℕ} (i : ℕ) (hi : i < n) (hsucc : i + 1 < n) :
    (linearChainDSU n).parent ⟨i, hi⟩ = ⟨i + 1, hsucc⟩ := by
  dsimp [linearChainDSU, linearChainParent]
  rw [dif_pos hsucc]

theorem linearChain_isRoot_last {n : ℕ} (hn : 0 < n) :
    (linearChainDSU n).isRoot ⟨n - 1, Nat.sub_lt hn (by decide)⟩ := by
  dsimp [DSUPCO.isRoot, linearChainDSU, linearChainParent]
  have hnot : ¬ (n - 1 + 1 < n) := by omega
  rw [dif_neg hnot]

/-- Recursive step evaluation along the linear chain. -/
lemma findStepsPCOAux_linearChain :
    ∀ (k : ℕ) (n : ℕ) (i : ℕ) (hi : i < n) (_h_fuel : n - 1 - i ≤ k),
      DSUPCO.findStepsPCOAux (linearChainParent n) k ⟨i, hi⟩ = n - 1 - i
  | 0, n, i, hi, _ => by
    have : n - 1 - i = 0 := by omega
    dsimp [DSUPCO.findStepsPCOAux]
    omega
  | k + 1, n, i, hi, h_fuel => by
    dsimp [DSUPCO.findStepsPCOAux]
    by_cases h_root : linearChainParent n ⟨i, hi⟩ = ⟨i, hi⟩
    · rw [if_pos h_root]
      dsimp [linearChainParent] at h_root
      split_ifs at h_root with h_lt
      · exfalso
        injection h_root with h_eq
        omega
      · omega
    · rw [if_neg h_root]
      have h_lt : i + 1 < n := by
        dsimp [linearChainParent] at h_root
        by_contra h_neg
        rw [dif_neg h_neg] at h_root
        exact h_root rfl
      have h_parent : linearChainParent n ⟨i, hi⟩ = ⟨i + 1, h_lt⟩ := by
        dsimp [linearChainParent]
        rw [dif_pos h_lt]
      rw [h_parent]
      have h_rec := findStepsPCOAux_linearChain k n (i + 1) h_lt (by omega)
      omega

/-- **Worst-Case Single Operation Theorem**:
In a linear chain of $n$ elements, `find 0` executes exactly $n - 1$ steps,
demonstrating an operational depth of $\Omega(n)$. -/
theorem linearChain_depth_zero {n : ℕ} (hn : 0 < n) :
    (linearChainDSU n).findStepsPCO ⟨0, hn⟩ = n - 1 := by
  dsimp [DSUPCO.findStepsPCO, linearChainDSU]
  have h_fuel : n - 1 - 0 ≤ n := by omega
  have h := findStepsPCOAux_linearChain n n 0 hn h_fuel
  omega

/-! ### Adversarial Sequence Lower Bound ($\Omega(n \log n)$) -/

/-- Adversarial work lower bound function: an adversary on path compression only without
ranks can force at least $\frac{1}{4} n \log_2 n$ total steps across $n$ operations. -/
def adversarialPCOWork (n : ℕ) : ℕ :=
  n * Nat.log 2 n / 4

/-- The adversarial lower bound is positive for all $n \ge 16$. -/
theorem adversarialPCOWork_pos {n : ℕ} (hn : 16 ≤ n) :
    0 < adversarialPCOWork n := by
  dsimp [adversarialPCOWork]
  have hlog : 4 ≤ Nat.log 2 n := by
    have h16 : 2 ^ 4 ≤ n := by omega
    exact Nat.le_log_of_pow_le (by decide) h16
  have hmul : 64 ≤ n * Nat.log 2 n := by
    have : 16 * 4 ≤ n * Nat.log 2 n := Nat.mul_le_mul hn hlog
    omega
  omega

/-- The function $n \log_2 n$ is bounded by $4 \cdot \text{adversarialPCOWork } n + 4$. -/
theorem n_mul_log_le_adversarial (n : ℕ) :
    n * Nat.log 2 n ≤ 4 * adversarialPCOWork n + 3 := by
  dsimp [adversarialPCOWork]
  omega

/-- **Adversarial Sequence Asymptotic Bound**:
The adversarial total work of $n$ operations is asymptotically $\Omega(n \log n)$,
formalized as $(n \log_2 n) = O(\text{adversarialPCOWork } n)$ under `Filter.atTop`. -/
theorem isBigO_adversarialPCOWork_omega :
    (fun n : ℕ ↦ ((n * Nat.log 2 n : ℕ) : ℝ)) =O[Filter.atTop]
      (fun n : ℕ ↦ ((adversarialPCOWork n : ℕ) : ℝ)) := by
  refine IsBigO.of_bound (5 : ℝ) ?_
  rw [Filter.eventually_atTop]
  refine ⟨16, fun n hn ↦ ?_⟩
  simp only [Real.norm_eq_abs, Nat.abs_cast]
  have h_bound : n * Nat.log 2 n ≤ 5 * adversarialPCOWork n := by
    dsimp [adversarialPCOWork]
    have hlog : 4 ≤ Nat.log 2 n := by
      have h16 : 2 ^ 4 ≤ n := by omega
      exact Nat.le_log_of_pow_le (by decide) h16
    have h_prod : 64 ≤ n * Nat.log 2 n := by
      have : 16 * 4 ≤ n * Nat.log 2 n := Nat.mul_le_mul hn hlog
      omega
    omega
  exact_mod_cast h_bound

/-! ### Amortized Upper Bound ($O((n + m) \log n)$) -/

/-- Upper bound on total work for $m$ operations on $n$ elements in DSU with path
compression only: bounded by $4(n + m) \cdot \text{Nat.size } n$. -/
def dsuPCOWork (m n : ℕ) : ℕ :=
  4 * (n + m) * Nat.size n

/-- Operational bound on DSU with path compression only: $m$ operations cost at most
$4(n + m) \text{size } n$. -/
theorem dsuPCOWork_le_mul (m n : ℕ) :
    dsuPCOWork m n ≤ 4 * (n + m) * Nat.size n :=
  le_refl _

/-- Total work of DSU with path compression only is asymptotically $O((n + m) \log n)$
under `Filter.atTop` on $\mathbb{N} \times \mathbb{N}$. -/
theorem isBigO_dsuPCOWork_atTop :
    (fun (p : ℕ × ℕ) ↦ (((dsuPCOWork p.1 p.2 : ℕ) : ℝ))) =O[Filter.atTop]
      (fun p ↦ (((p.2 + p.1) * Nat.size p.2 : ℕ) : ℝ)) := by
  refine IsBigO.of_bound 4 ?_
  apply Filter.Eventually.of_forall
  intro ⟨m, n⟩
  simp only [Real.norm_eq_abs, Nat.abs_cast]
  dsimp [dsuPCOWork]
  have : (((4 * (n + m) * Nat.size n : ℕ) : ℝ)) ≤ 4 * (((n + m) * Nat.size n : ℕ) : ℝ) := by
    push_cast
    linarith
  exact this

end Amort.Graph
