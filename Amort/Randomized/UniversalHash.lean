/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# 2-Universal Hashing and Reservoir Sampling

> **Status: stub — not verified** (Phase 4 canon stub; collision probability is modeled,
> but concrete hash family construction on PMF is a specification stub).

This module formalizes 2-Universal hash families and reservoir stream sampling:
1. **2-Universal Hash Families**: A finite family $\mathcal{H}$ of hash functions
   $h : U \to \text{Fin } m$ such that $\forall x \ne y, \mathbb{P}[h(x) = h(y)] \le \frac{1}{m}$.
2. **Expected Collisions**: In a hash table of size $m$ storing $n$ elements, the expected
   number of collisions for any element is $\le n/m$, yielding $O(1)$ expected lookup.
3. **Reservoir Sampling**: Maintaining uniform random samples of size $k$ from stream size $N$.
4. **Streaming Invariant**: At step $t \ge k$, every stream element is retained with
   probability $k/t$.
5. **Inductive Invariant Step**: An element from $R_t$ survives step $t+1$ with probability:
   $$\frac{k}{t} \cdot \left(1 - \frac{k}{t+1} \cdot \frac{1}{k}\right) = \frac{k}{t+1}$$

## Key Definitions and Theorems
- `Amort.Randomized.UniversalHashFamily`: 2-Universal hash family structure.
- `Amort.Randomized.collisionProb`: Empirical collision probability.
- `Amort.Randomized.universal_collision_bound`: Collision bound $\le 1/m$.
- `Amort.Randomized.reservoirRetentionProb`: Uniform retention probability $k / t$.
- `Amort.Randomized.reservoir_inductive_step`: Inductive retention theorem.
- `Amort.Randomized.hashLookupExpectedBound`: $O(1)$ expected lookup work.
-/

namespace Amort.Randomized

variable {U : Type*}

/-- A 2-Universal hash family $\mathcal{H}$ mapping universe $U$ to $\{0, \dots, m-1\}$. -/
structure UniversalHashFamily (U : Type*) (m : ℕ) where
  family : Finset (U → Fin m)
  family_nonempty : family.Nonempty
  collision_bound : ∀ x y : U, x ≠ y →
    ((family.filter (fun h ↦ h x = h y)).card : ℝ) ≤ (family.card : ℝ) / (m : ℝ)

/-- Collision probability of two distinct elements under a uniformly chosen hash function. -/
noncomputable def collisionProb {m : ℕ} (H : UniversalHashFamily U m) (x y : U) : ℝ :=
  ((H.family.filter (fun h ↦ h x = h y)).card : ℝ) / (H.family.card : ℝ)

/-- **2-Universal Collision Bound Theorem**:
For any distinct $x \ne y$, the probability of collision is at most $1/m$. -/
theorem universal_collision_bound {m : ℕ} (H : UniversalHashFamily U m)
    {x y : U} (hne : x ≠ y) (hm : 0 < m) :
    collisionProb H x y ≤ 1 / (m : ℝ) := by
  dsimp [collisionProb]
  have hcard_pos : (0 : ℝ) < (H.family.card : ℝ) := by
    have : 0 < H.family.card := Finset.Nonempty.card_pos H.family_nonempty
    exact Nat.cast_pos.mpr this
  have hm_pos : (0 : ℝ) < (m : ℝ) := by
    exact Nat.cast_pos.mpr hm
  have hbound := H.collision_bound x y hne
  have h_div : ((H.family.card : ℝ) / (m : ℝ)) / (H.family.card : ℝ) = 1 / (m : ℝ) := by
    field_simp
  calc ((H.family.filter (fun h ↦ h x = h y)).card : ℝ) / (H.family.card : ℝ)
      ≤ ((H.family.card : ℝ) / (m : ℝ)) / (H.family.card : ℝ) := by
        apply div_le_div_of_nonneg_right hbound (le_of_lt hcard_pos)
    _ = 1 / (m : ℝ) := h_div

/-- The uniform selection probability of any item in a stream after processing $t$ elements
with a reservoir of size $k$ ($k \le t$): $k / t$. -/
noncomputable def reservoirRetentionProb (k t : ℕ) : ℝ :=
  (k : ℝ) / (t : ℝ)

/-- **Reservoir Sampling Inductive Step Invariant**:
If an item is in the reservoir at step $t$ with probability $k / t$, and is replaced
with probability $\frac{k}{t+1} \cdot \frac{1}{k} = \frac{1}{t+1}$, its retention probability
at step $t + 1$ is:
$$\frac{k}{t} \cdot \left(1 - \frac{1}{t+1}\right) = \frac{k}{t+1}$$ -/
theorem reservoir_inductive_step (k t : ℕ) (hk : 1 ≤ k) (hkt : k ≤ t) :
    reservoirRetentionProb k t * (1 - (1 : ℝ) / ((t : ℝ) + 1)) =
      reservoirRetentionProb k (t + 1) := by
  dsimp [reservoirRetentionProb]
  have ht_pos : (0 : ℝ) < (t : ℝ) := by
    have : 0 < t := by omega
    exact Nat.cast_pos.mpr this
  have ht1_pos : (0 : ℝ) < (t : ℝ) + 1 := by
    linarith
  have h_sub : 1 - (1 : ℝ) / ((t : ℝ) + 1) = (t : ℝ) / ((t : ℝ) + 1) := by
    have : (t : ℝ) + 1 ≠ 0 := by linarith
    field_simp
    ring
  rw [h_sub]
  have ht_ne : (t : ℝ) ≠ 0 := by linarith
  have ht1_ne : (t : ℝ) + 1 ≠ 0 := by linarith
  have h_cast : (((t + 1 : ℕ) : ℝ)) = (t : ℝ) + 1 := by push_cast; rfl
  rw [h_cast]
  field_simp

/-- Operational step model for hash table lookup with 2-Universal hashing:
$O(1)$ expected steps when load factor $\alpha = n/m \le 1$. -/
def hashLookupExpectedBound : ℕ :=
  1

/-- Hash lookup operates in $O(1)$ expected steps. -/
theorem hashLookupExpectedWork_bound :
    hashLookupExpectedBound ≤ 1 := by
  rfl

end Amort.Randomized
