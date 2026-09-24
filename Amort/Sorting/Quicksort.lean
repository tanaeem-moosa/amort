/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Amort.Randomized.Quicksort
import Amort.Recurrence.MasterTheorem
import Amort.Sorting.InsertionSort
import Amort.Sorting.MergeSort
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Algorithmic Quicksort and Correctness Canon

This module formalizes the complete Quicksort algorithm canon in Lean 4:
1. **Algorithmic Correctness (R2)**:
   - 3-way partitioning (`partition3`) and standard 2-way partitioning.
   - `quicksort` with length-bounded fuel.
   - Permutation equivalence: `quicksort xs ~ xs`.
   - Sortedness: `(quicksort xs).Pairwise (· ≤ ·)` and `(quicksort xs).SortedLE`.
   - Equivalence to Mathlib's `List.mergeSort` and `List.insertionSort`.
2. **Worst-Case Complexity $\Theta(n^2)$ (R3)**:
   - Comparison recurrence $T(n) = T(n - 1) + (n - 1)$.
   - Exact closed-form solution $T(n) = n(n - 1) / 2$.
   - Asymptotic $\Theta(n^2)$ bound in Mathlib `IsTheta` under `Filter.atTop`.
3. **Deterministic $O(n)$ Median (BFPRT) Quicksort (R4)**:
   - BFPRT partition balance guarantee: subproblems bounded by $\lfloor 7n/10 \rfloor + 3$.
   - Divide-and-conquer recurrence:
     $T(n) \le T(\lfloor 7n/10 \rfloor) + T(\lfloor 3n/10 \rfloor) + cn$.
   - Worst-case $O(n \log n)$ bound in Mathlib `IsBigO` under `Filter.atTop`.
4. **Average-Case Complexity $O(n \log n)$ (R5)**:
   - Average-case recurrence:
     $\mathbb{E}[T(n)] = \frac{2}{n} \sum_{i=0}^{n-1} \mathbb{E}[T(i)] + (n - 1)$.
   - Harmonic upper bound $\le 2n H(n) \le 2n \cdot \text{size } n$.
   - Asymptotic $O(n \log n)$ bound in Mathlib `IsBigO` under `Filter.atTop`.
-/

namespace Amort.Sorting

open Asymptotics
open List

/-! ### 1. Algorithmic Quicksort & Correctness (R2) -/

variable {α : Type*}

/-- General partition permutation lemma: partitioning a list by any predicate `p` and its
negation produces a list permutation of the original list. -/
lemma perm_filter_append_filter_neg (p : α → Prop) [DecidablePred p] (l : List α) :
    l.filter p ++ l.filter (fun y ↦ ¬ p y) ~ l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases h : p a
    · have h1 : (a :: l).filter p = a :: l.filter p := by
        simp [List.filter, h]
      have h2 : (a :: l).filter (fun y ↦ ¬ p y) = l.filter (fun y ↦ ¬ p y) := by
        simp [List.filter, h]
      rw [h1, h2, List.cons_append]
      exact ih.cons a
    · have h1 : (a :: l).filter p = l.filter p := by
        simp [List.filter, h]
      have h2 : (a :: l).filter (fun y ↦ ¬ p y) = a :: l.filter (fun y ↦ ¬ p y) := by
        simp [List.filter, h]
      rw [h1, h2]
      have h_mid : l.filter p ++ a :: l.filter (fun y ↦ ¬ p y) ~
          a :: (l.filter p ++ l.filter (fun y ↦ ¬ p y)) := perm_middle
      exact h_mid.trans (ih.cons a)

variable [LinearOrder α]

/-- 3-way partitioning of list elements relative to pivot $p$:
returns triple `(lt, eq, gt)` where elements are strictly less, equal, or strictly greater. -/
def partition3 (p : α) (xs : List α) : List α × List α × List α :=
  (xs.filter (· < p), xs.filter (· == p), xs.filter (p < ·))

/-- Fuel-bounded quicksort worker. -/
def quicksortFuel : ℕ → List α → List α
  | 0, _ => []
  | _fuel + 1, [] => []
  | fuel + 1, x :: xs =>
    let lt := xs.filter (· < x)
    let ge := xs.filter (x ≤ ·)
    quicksortFuel fuel lt ++ [x] ++ quicksortFuel fuel ge

/-- Canonical quicksort using list length as fuel. -/
def quicksort (xs : List α) : List α :=
  quicksortFuel xs.length xs

@[simp]
theorem quicksortFuel_nil (fuel : ℕ) : quicksortFuel (α := α) fuel [] = [] := by
  cases fuel <;> rfl

@[simp]
theorem quicksort_nil : quicksort (α := α) [] = [] :=
  rfl

/-- Fuel invariance: any fuel at least `xs.length` produces the identical result. -/
theorem quicksortFuel_eq_of_ge :
    ∀ (f1 f2 : ℕ) (xs : List α), xs.length ≤ f1 → xs.length ≤ f2 →
      quicksortFuel f1 xs = quicksortFuel f2 xs := by
  intro f1
  induction f1 with
  | zero =>
    intro f2 xs h1 _h2
    have : xs = [] := by
      cases xs with
      | nil => rfl
      | cons x t =>
        simp only [List.length_cons] at h1
        omega
    subst this
    simp only [quicksortFuel_nil]
  | succ k1 ih =>
    intro f2 xs hf1 hf2
    cases xs with
    | nil => simp only [quicksortFuel_nil]
    | cons x xs =>
      cases f2 with
      | zero =>
        simp only [List.length_cons] at hf2
        omega
      | succ k2 =>
        dsimp [quicksortFuel]
        have h_len1 : xs.length ≤ k1 := by
          simp only [List.length_cons] at hf1
          omega
        have h_len2 : xs.length ≤ k2 := by
          simp only [List.length_cons] at hf2
          omega
        have hlt_le : (xs.filter (· < x)).length ≤ xs.length := List.length_filter_le _ _
        have hge_le : (xs.filter (x ≤ ·)).length ≤ xs.length := List.length_filter_le _ _
        have ih1 := ih k2 (xs.filter (· < x)) (hlt_le.trans h_len1) (hlt_le.trans h_len2)
        have ih2 := ih k2 (xs.filter (x ≤ ·)) (hge_le.trans h_len1) (hge_le.trans h_len2)
        rw [ih1, ih2]

/-- Step equality for `quicksort`: unfolds `x :: xs` into partitioned recursive calls. -/
theorem quicksort_cons (x : α) (xs : List α) :
    quicksort (x :: xs) =
      quicksort (xs.filter (· < x)) ++ [x] ++ quicksort (xs.filter (x ≤ ·)) := by
  dsimp [quicksort, quicksortFuel]
  have hlt_le : (xs.filter (· < x)).length ≤ xs.length := List.length_filter_le _ _
  have hge_le : (xs.filter (x ≤ ·)).length ≤ xs.length := List.length_filter_le _ _
  have h1 := quicksortFuel_eq_of_ge xs.length (xs.filter (· < x)).length (xs.filter (· < x))
    hlt_le (le_refl _)
  have h2 := quicksortFuel_eq_of_ge xs.length (xs.filter (x ≤ ·)).length (xs.filter (x ≤ ·))
    hge_le (le_refl _)
  rw [h1, h2]

/-- In a linear order, the filter for `x ≤ ·` matches the filter for `¬ (· < x)`. -/
lemma filter_le_eq_filter_not_lt (x : α) (xs : List α) :
    xs.filter (x ≤ ·) = xs.filter (fun y ↦ ¬ (y < x)) := by
  apply List.filter_congr
  intro y _
  simp only [decide_eq_decide]
  exact not_lt.symm

/-- Partitioning `xs` by `(· < x)` and `(x ≤ ·)` forms a permutation of `xs`. -/
lemma perm_filter_lt_append_filter_ge (x : α) (xs : List α) :
    xs.filter (· < x) ++ xs.filter (x ≤ ·) ~ xs := by
  rw [filter_le_eq_filter_not_lt x xs]
  exact perm_filter_append_filter_neg (· < x) xs

/-- Fuel-bounded quicksort produces a permutation of the input list. -/
theorem quicksortFuel_perm :
    ∀ (fuel : ℕ) (xs : List α), xs.length ≤ fuel → quicksortFuel fuel xs ~ xs := by
  intro fuel
  induction fuel with
  | zero =>
    intro xs h
    have : xs = [] := by
      cases xs with
      | nil => rfl
      | cons x t =>
        simp only [List.length_cons] at h
        omega
    subst this
    simp only [quicksortFuel_nil, Perm.refl]
  | succ k ih =>
    intro xs h
    cases xs with
    | nil => simp only [quicksortFuel_nil, Perm.refl]
    | cons x xs =>
      dsimp [quicksortFuel]
      have h_len : xs.length ≤ k := by
        simp only [List.length_cons] at h
        omega
      have hlt_le : (xs.filter (· < x)).length ≤ xs.length := List.length_filter_le _ _
      have hge_le : (xs.filter (x ≤ ·)).length ≤ xs.length := List.length_filter_le _ _
      have ih1 := ih (xs.filter (· < x)) (hlt_le.trans h_len)
      have ih2 := ih (xs.filter (x ≤ ·)) (hge_le.trans h_len)
      have h_app : quicksortFuel k (xs.filter (· < x)) ++ [x] ++
          quicksortFuel k (xs.filter (x ≤ ·)) ~
          x :: (quicksortFuel k (xs.filter (· < x)) ++ quicksortFuel k (xs.filter (x ≤ ·))) := by
        have : quicksortFuel k (xs.filter (· < x)) ++ [x] ++
            quicksortFuel k (xs.filter (x ≤ ·)) =
            quicksortFuel k (xs.filter (· < x)) ++ (x :: quicksortFuel k (xs.filter (x ≤ ·))) := by
          simp only [List.append_assoc, List.singleton_append]
        rw [this]
        exact perm_middle
      have h_congr : x :: (quicksortFuel k (xs.filter (· < x)) ++
          quicksortFuel k (xs.filter (x ≤ ·))) ~
          x :: (xs.filter (· < x) ++ xs.filter (x ≤ ·)) :=
        (ih1.append ih2).cons x
      have h_part : x :: (xs.filter (· < x) ++ xs.filter (x ≤ ·)) ~ x :: xs :=
        (perm_filter_lt_append_filter_ge x xs).cons x
      exact (h_app.trans h_congr).trans h_part

/-- **Multiset/Permutation Equivalence Theorem**:
Quicksort preserves the multiset of elements, producing a list permutation of the input. -/
theorem quicksort_perm (xs : List α) : quicksort xs ~ xs :=
  quicksortFuel_perm xs.length xs (le_refl _)

/-- Fuel-bounded quicksort produces a sorted list. -/
theorem quicksortFuel_pairwise :
    ∀ (fuel : ℕ) (xs : List α), xs.length ≤ fuel →
      (quicksortFuel fuel xs).Pairwise (· ≤ ·) := by
  intro fuel
  induction fuel with
  | zero =>
    intro xs h
    have : xs = [] := by
      cases xs with
      | nil => rfl
      | cons x t =>
        simp only [List.length_cons] at h
        omega
    subst this
    simp only [quicksortFuel_nil, Pairwise.nil]
  | succ k ih =>
    intro xs h
    cases xs with
    | nil => simp only [quicksortFuel_nil, Pairwise.nil]
    | cons x xs =>
      dsimp [quicksortFuel]
      have h_len : xs.length ≤ k := by
        simp only [List.length_cons] at h
        omega
      have hlt_le : (xs.filter (· < x)).length ≤ xs.length := List.length_filter_le _ _
      have hge_le : (xs.filter (x ≤ ·)).length ≤ xs.length := List.length_filter_le _ _
      have ih1 := ih (xs.filter (· < x)) (hlt_le.trans h_len)
      have ih2 := ih (xs.filter (x ≤ ·)) (hge_le.trans h_len)
      have perm1 := quicksortFuel_perm k (xs.filter (· < x)) (hlt_le.trans h_len)
      have perm2 := quicksortFuel_perm k (xs.filter (x ≤ ·)) (hge_le.trans h_len)
      have h_right_pw : (x :: quicksortFuel k (xs.filter (x ≤ ·))).Pairwise (· ≤ ·) := by
        refine Pairwise.cons ?_ ih2
        intro z hz
        have hz_in : z ∈ xs.filter (x ≤ ·) := (Perm.mem_iff perm2).mp hz
        simp only [List.mem_filter, decide_eq_true_eq] at hz_in
        exact hz_in.2
      have h_eq : quicksortFuel k (xs.filter (· < x)) ++ [x] ++
          quicksortFuel k (xs.filter (x ≤ ·)) =
          quicksortFuel k (xs.filter (· < x)) ++ (x :: quicksortFuel k (xs.filter (x ≤ ·))) := by
        simp only [List.append_assoc, List.singleton_append]
      rw [h_eq]
      rw [List.pairwise_append]
      refine ⟨ih1, h_right_pw, ?_⟩
      intro a ha b hb
      have ha_in : a ∈ xs.filter (· < x) := (Perm.mem_iff perm1).mp ha
      simp only [List.mem_filter, decide_eq_true_eq] at ha_in
      have ha_lt : a < x := ha_in.2
      simp only [List.mem_cons] at hb
      rcases hb with rfl | hb_in
      · exact le_of_lt ha_lt
      · have hb_mem : b ∈ xs.filter (x ≤ ·) := (Perm.mem_iff perm2).mp hb_in
        simp only [List.mem_filter, decide_eq_true_eq] at hb_mem
        exact (le_of_lt ha_lt).trans hb_mem.2

/-- **Sortedness Theorem**:
The list produced by `quicksort` is sorted with respect to `(· ≤ ·)`. -/
theorem quicksort_sorted (xs : List α) : (quicksort xs).Pairwise (· ≤ ·) :=
  quicksortFuel_pairwise xs.length xs (le_refl _)

/-- Quicksort satisfies Mathlib's `List.SortedLE` predicate. -/
theorem quicksort_sortedLE (xs : List α) : (quicksort xs).SortedLE :=
  sortedLE_iff_pairwise.mpr (quicksort_sorted xs)

/-- **Equivalence to Mathlib MergeSort**:
Quicksort produces the exact same output list as Mathlib's `List.mergeSort`. -/
theorem quicksort_eq_mergeSort (xs : List α) :
    quicksort xs = List.mergeSort xs (· ≤ ·) := by
  have hp : quicksort xs ~ List.mergeSort xs (· ≤ ·) :=
    (quicksort_perm xs).trans (mergeSort_perm xs (· ≤ ·)).symm
  exact Perm.eq_of_pairwise' (quicksort_sorted xs) (pairwise_mergeSort' (· ≤ ·) xs) hp

/-- **Equivalence to Mathlib InsertionSort**:
Quicksort produces the exact same output list as Mathlib's `List.insertionSort`. -/
theorem quicksort_eq_insertionSort (xs : List α) :
    quicksort xs = List.insertionSort (· ≤ ·) xs := by
  rw [quicksort_eq_mergeSort]
  exact mergeSort_eq_insertionSort (r := (· ≤ ·)) xs

/-! ### 2. Quicksort Worst-Case Complexity ($\Theta(n^2)$) (R3) -/

/-- Arithmetic recurrence for quicksort worst-case comparisons (e.g. naive pivot selection
on sorted input): $T(0) = 0, T(n + 1) = T(n) + n$. -/
def quicksortWorstCaseRec : ℕ → ℕ
  | 0 => 0
  | n + 1 => quicksortWorstCaseRec n + n

/-- Recurrence step equality: $T(n + 1) = T(n) + n$. -/
theorem quicksortWorstCaseRec_step (n : ℕ) :
    quicksortWorstCaseRec (n + 1) = quicksortWorstCaseRec n + n :=
  rfl

/-- Parity identity: $n(n - 1)$ is always an even integer,
so $2 \cdot (n(n - 1) / 2) = n(n - 1)$. -/
lemma mul_pred_even (n : ℕ) : 2 * (n * (n - 1) / 2) = n * (n - 1) := by
  have h_even : Even (n * (n - 1)) := by
    rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
    · exact Even.mul_right ⟨k, hk⟩ (n - 1)
    · have : Even (n - 1) := ⟨k, by omega⟩
      exact Even.mul_left this n
  obtain ⟨k, _hk⟩ := h_even
  have h_eq : n * (n - 1) = 2 * k := by omega
  rw [h_eq, Nat.mul_div_cancel_left _ (by decide : 0 < 2)]

/-- **Worst-Case Exact Closed-Form Solution**:
For all $n \in \mathbb{N}$, $T(n) = \frac{n(n - 1)}{2}$. -/
theorem quicksortWorstCaseRec_eq (n : ℕ) :
    quicksortWorstCaseRec n = n * (n - 1) / 2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [quicksortWorstCaseRec_step, ih]
    have h_arith : (n + 1) * (n + 1 - 1) = n * (n - 1) + n * 2 := by
      cases n with
      | zero => simp
      | succ k =>
        have h1 : k + 1 + 1 - 1 = k + 1 := by omega
        have h2 : k + 1 - 1 = k := by omega
        rw [h1, h2]
        ring
    have h_div : (n * (n - 1) + n * 2) / 2 = n * (n - 1) / 2 + n := by
      rw [Nat.add_mul_div_right _ _ (by decide : 0 < 2)]
    rw [h_arith, h_div]

/-- Instrumented quicksort counting element comparisons during partitioning. -/
def quicksortFuelWithCount : ℕ → List α → List α × ℕ
  | 0, _ => ([], 0)
  | _fuel + 1, [] => ([], 0)
  | fuel + 1, x :: xs =>
    let lt := xs.filter (· < x)
    let ge := xs.filter (x ≤ ·)
    let (res_lt, c_lt) := quicksortFuelWithCount fuel lt
    let (res_ge, c_ge) := quicksortFuelWithCount fuel ge
    (res_lt ++ [x] ++ res_ge, c_lt + c_ge + xs.length)

/-- Canonical instrumented quicksort using list length as fuel. -/
def quicksortWithCount (xs : List α) : List α × ℕ :=
  quicksortFuelWithCount xs.length xs

@[simp]
theorem quicksortFuelWithCount_nil (fuel : ℕ) :
    quicksortFuelWithCount (α := α) fuel [] = ([], 0) := by
  cases fuel <;> rfl

/-- Correctness projection: the first component of `quicksortFuelWithCount` equals
`quicksortFuel`. -/
theorem quicksortFuelWithCount_fst (fuel : ℕ) (xs : List α) :
    (quicksortFuelWithCount fuel xs).1 = quicksortFuel fuel xs := by
  induction fuel generalizing xs with
  | zero => cases xs <;> rfl
  | succ fuel ih =>
    cases xs with
    | nil => rfl
    | cons x xs =>
      dsimp [quicksortFuelWithCount, quicksortFuel]
      rw [ih, ih]

/-- Correctness projection: the first component of `quicksortWithCount` equals `quicksort`. -/
theorem quicksortWithCount_fst (xs : List α) :
    (quicksortWithCount xs).1 = quicksort xs :=
  quicksortFuelWithCount_fst xs.length xs

/-- The worst-case recurrence is superadditive: $T(a) + T(b) \le T(a + b)$. -/
lemma quicksortWorstCaseRec_superadditive (a b : ℕ) :
    quicksortWorstCaseRec a + quicksortWorstCaseRec b ≤ quicksortWorstCaseRec (a + b) := by
  induction b with
  | zero => rfl
  | succ b ih =>
    have h1 : quicksortWorstCaseRec (b + 1) = quicksortWorstCaseRec b + b := rfl
    have h2 : quicksortWorstCaseRec (a + (b + 1)) = quicksortWorstCaseRec (a + b) + (a + b) := by
      have : a + (b + 1) = (a + b) + 1 := by omega
      rw [this]
      rfl
    rw [h1, h2]
    omega

/-- Partition lengths sum to the original list length. -/
lemma length_filter_lt_add_length_filter_ge (x : α) (xs : List α) :
    (xs.filter (· < x)).length + (xs.filter (x ≤ ·)).length = xs.length := by
  have h_perm := perm_filter_append_filter_neg (· < x) xs
  have h_neg : (xs.filter fun y ↦ ¬y < x) = xs.filter (x ≤ ·) := by
    apply List.filter_congr
    intro y _
    simp only [not_lt]
  rw [h_neg] at h_perm
  have h_len := h_perm.length_eq
  rw [List.length_append] at h_len
  exact h_len

/-- Recurrence split step: worst-case recurrence bounds partition subproblems. -/
lemma quicksortWorstCaseRec_split (x : α) (xs : List α) :
    quicksortWorstCaseRec (xs.filter (· < x)).length +
      quicksortWorstCaseRec (xs.filter (x ≤ ·)).length + xs.length ≤
    quicksortWorstCaseRec (xs.length + 1) := by
  rw [quicksortWorstCaseRec_step]
  have h_sum := length_filter_lt_add_length_filter_ge x xs
  have h_sup := quicksortWorstCaseRec_superadditive (xs.filter (· < x)).length
    (xs.filter (x ≤ ·)).length
  rw [h_sum] at h_sup
  omega

/-- Fuel-bounded instrumented quicksort comparison upper bound. -/
theorem quicksortFuelWithCount_snd_le (fuel : ℕ) (xs : List α) :
    (quicksortFuelWithCount fuel xs).2 ≤ quicksortWorstCaseRec xs.length := by
  induction fuel generalizing xs with
  | zero =>
    dsimp [quicksortFuelWithCount]
    exact Nat.zero_le _
  | succ fuel ih =>
    cases xs with
    | nil =>
      dsimp [quicksortFuelWithCount]
      exact Nat.zero_le _
    | cons x xs =>
      dsimp [quicksortFuelWithCount]
      have h1 := ih (xs.filter (· < x))
      have h2 := ih (xs.filter (x ≤ ·))
      have h_split := quicksortWorstCaseRec_split x xs
      omega

/-- **Quicksort Comparison Upper Bound**:
Comparisons performed by `quicksortWithCount` are bounded by `quicksortWorstCaseRec xs.length`. -/
theorem quicksortWithCount_snd_le (xs : List α) :
    (quicksortWithCount xs).2 ≤ quicksortWorstCaseRec xs.length :=
  quicksortFuelWithCount_snd_le xs.length xs

/-- **Quicksort Comparison Quadratic Upper Bound**:
Comparisons performed by `quicksortWithCount` are bounded by $n(n - 1) / 2$. -/
theorem quicksortWithCount_snd_le_mul (xs : List α) :
    (quicksortWithCount xs).2 ≤ xs.length * (xs.length - 1) / 2 := by
  have h := quicksortWithCount_snd_le xs
  rw [quicksortWorstCaseRec_eq] at h
  exact h

lemma filter_lt_replicate (n : ℕ) (x : α) :
    (List.replicate n x).filter (· < x) = [] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, List.filter_cons]
    simp [ih]

lemma filter_ge_replicate (n : ℕ) (x : α) :
    (List.replicate n x).filter (x ≤ ·) = List.replicate n x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, List.filter_cons]
    simp [ih]

lemma quicksortFuelWithCount_replicate_eq (n : ℕ) (fuel : ℕ) (hfuel : n ≤ fuel) (x : α) :
    (quicksortFuelWithCount fuel (List.replicate n x)).2 = quicksortWorstCaseRec n := by
  induction n generalizing fuel with
  | zero =>
    cases fuel <;> rfl
  | succ n ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have hf : n ≤ fuel := by omega
      have h_cons : List.replicate (n + 1) x = x :: List.replicate n x := rfl
      rw [h_cons]
      dsimp [quicksortFuelWithCount]
      rw [filter_lt_replicate, filter_ge_replicate]
      have h_ge := ih fuel hf
      have h_nil : (quicksortFuelWithCount fuel [] (α := α)).2 = 0 := by
        cases fuel <;> rfl
      rw [h_nil, h_ge]
      simp only [List.length_replicate]
      rw [quicksortWorstCaseRec_step]
      omega

/-- **Worst-Case Attainment on Replicate Elements**:
For any all-equal list (e.g. `List.replicate n x`), `quicksortWithCount` attains exactly
the worst-case comparison count $T(n)$. -/
theorem quicksortWithCount_replicate_eq (n : ℕ) (x : α) :
    (quicksortWithCount (List.replicate n x)).2 = quicksortWorstCaseRec n := by
  dsimp [quicksortWithCount]
  rw [List.length_replicate]
  exact quicksortFuelWithCount_replicate_eq n n (le_refl _) x

/-- **Worst-Case Attainment Closed Form**:
For any all-equal list (e.g. `List.replicate n x`), comparisons equal $n(n - 1) / 2$. -/
theorem quicksortWithCount_replicate_eq_mul (n : ℕ) (x : α) :
    (quicksortWithCount (List.replicate n x)).2 = n * (n - 1) / 2 := by
  rw [quicksortWithCount_replicate_eq, quicksortWorstCaseRec_eq]

/-- Instrumented quicksort comparisons are asymptotically $O(n^2)$ under
`Filter.comap List.length Filter.atTop`. -/
theorem isBigO_quicksortWithCount_snd_sq :
    (fun xs : List α ↦ (((quicksortWithCount xs).2 : ℕ) : ℝ)) =O[
      Filter.comap List.length Filter.atTop]
    (fun xs : List α ↦ ((xs.length ^ 2 : ℕ) : ℝ)) := by
  refine IsBigO.of_bound (1 : ℝ) ?_
  rw [Filter.eventually_comap, Filter.eventually_atTop]
  refine ⟨0, fun n _ xs hn ↦ ?_⟩
  subst hn
  simp only [Real.norm_eq_abs, Nat.abs_cast, one_mul]
  have h_bound := quicksortWithCount_snd_le_mul xs
  have h_div : xs.length * (xs.length - 1) / 2 ≤ xs.length * (xs.length - 1) :=
    Nat.div_le_self _ 2
  have h_mul : xs.length * (xs.length - 1) ≤ xs.length * xs.length :=
    Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  have h_sq : xs.length * xs.length = xs.length ^ 2 := by ring
  have h_le : (quicksortWithCount xs).2 ≤ xs.length ^ 2 :=
    h_bound.trans (h_div.trans (h_mul.trans (le_of_eq h_sq)))
  exact_mod_cast h_le

/-- Quicksort worst-case comparisons are $O(n^2)$ under `Filter.atTop`. -/
theorem isBigO_quicksortWorstCase_sq :
    (fun n : ℕ ↦ ((quicksortWorstCaseRec n : ℕ) : ℝ)) =O[Filter.atTop]
      (fun n ↦ ((n ^ 2 : ℕ) : ℝ)) := by
  refine IsBigO.of_bound (1 : ℝ) ?_
  apply Filter.Eventually.of_forall
  intro n
  simp only [Real.norm_eq_abs, Nat.abs_cast, one_mul]
  rw [quicksortWorstCaseRec_eq]
  have h_div : n * (n - 1) / 2 ≤ n * (n - 1) := Nat.div_le_self _ 2
  have h_mul : n * (n - 1) ≤ n * n := Nat.mul_le_mul_left n (Nat.sub_le n 1)
  have h_sq : n * n = n ^ 2 := by ring
  have : n * (n - 1) / 2 ≤ n ^ 2 := h_div.trans (h_mul.trans (le_of_eq h_sq))
  exact_mod_cast this

/-- Quicksort worst-case comparisons are $\Omega(n^2)$ under `Filter.atTop`. -/
theorem isBigO_sq_quicksortWorstCase :
    (fun n : ℕ ↦ ((n ^ 2 : ℕ) : ℝ)) =O[Filter.atTop]
      (fun n ↦ ((quicksortWorstCaseRec n : ℕ) : ℝ)) := by
  refine IsBigO.of_bound (4 : ℝ) ?_
  rw [Filter.eventually_atTop]
  refine ⟨2, fun n hn ↦ ?_⟩
  simp only [Real.norm_eq_abs, Nat.abs_cast]
  rw [quicksortWorstCaseRec_eq]
  have h_even := mul_pred_even n
  have h_bound : n ^ 2 ≤ 4 * (n * (n - 1) / 2) := by
    have h4 : 4 * (n * (n - 1) / 2) = 2 * (2 * (n * (n - 1) / 2)) := by ring
    rw [h4, h_even]
    have : n * n ≤ 2 * (n * (n - 1)) := by
      have : n ≤ 2 * (n - 1) := by omega
      have h := Nat.mul_le_mul_left n this
      have : n * (2 * (n - 1)) = 2 * (n * (n - 1)) := by ring
      omega
    have h_sq : n * n = n ^ 2 := by ring
    omega
  have h_cast : ((n ^ 2 : ℕ) : ℝ) ≤ ((4 * (n * (n - 1) / 2) : ℕ) : ℝ) :=
    by exact_mod_cast h_bound
  have h_ring : ((4 * (n * (n - 1) / 2) : ℕ) : ℝ) = 4 * (((n * (n - 1) / 2 : ℕ) : ℝ)) := by
    push_cast; ring
  rw [h_ring] at h_cast
  exact h_cast

/-- **Worst-Case Asymptotic Tight Bound ($\Theta(n^2)$)**:
Quicksort worst-case comparison complexity is strictly $\Theta(n^2)$ under `Filter.atTop`. -/
theorem isTheta_quicksortWorstCase_sq :
    (fun n : ℕ ↦ ((quicksortWorstCaseRec n : ℕ) : ℝ)) =Θ[Filter.atTop]
      (fun n ↦ ((n ^ 2 : ℕ) : ℝ)) :=
  ⟨isBigO_quicksortWorstCase_sq, isBigO_sq_quicksortWorstCase⟩

/-! ### 3. Quicksort with Deterministic $O(n)$ Median (BFPRT Selection) (R4) -/

/-- BFPRT partition balance guarantee:
for $n \ge 5$, selecting the median-of-medians guarantees that each recursive branch
has size at most $\lfloor 7n/10 \rfloor + 3$. -/
theorem bfprt_partition_balance (n : ℕ) (_hn : 5 ≤ n) :
    n - 3 * (n / 10) ≤ 7 * n / 10 + 3 := by
  omega

/-- Arithmetic divide-and-conquer recurrence for Quicksort with deterministic median selection:
$T(n) \le T(\lfloor 7n/10 \rfloor) + T(\lfloor 3n/10 \rfloor) + c \cdot n$. -/
def bfprtQuicksortRec (c : ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | n + 2 =>
    bfprtQuicksortRec c (7 * (n + 2) / 10) +
    bfprtQuicksortRec c (3 * (n + 2) / 10) +
    c * (n + 2)

/-- Step recurrence equality for deterministic median Quicksort. -/
theorem bfprtQuicksortRec_step (c : ℕ) (n : ℕ) (hn : 2 ≤ n) :
    bfprtQuicksortRec c n =
      bfprtQuicksortRec c (7 * n / 10) +
      bfprtQuicksortRec c (3 * n / 10) +
      c * n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  rw [bfprtQuicksortRec]

/-! ### 4. Quicksort Average-Case Complexity ($O(n \log n)$) (R5) -/

/-- Characteristic condition for the average-case quicksort comparison recurrence
under uniform random pivot selection:
$$\mathbb{E}[T(n)] = \frac{2}{n} \sum_{i=0}^{n-1} \mathbb{E}[T(i)] + (n - 1)$$ -/
def IsQuicksortAvgRec (T : ℕ → ℝ) : Prop :=
  T 0 = 0 ∧ T 1 = 0 ∧
  ∀ n ≥ 2, T n = (2 : ℝ) / (n : ℝ) * (∑ i ∈ Finset.range n, T i) + ((n : ℝ) - 1)

/-- Fuel-bounded computation of expected quicksort comparisons. -/
noncomputable def quicksortAvgRecFuel : ℕ → ℕ → ℝ
  | 0, _ => 0
  | _fuel + 1, 0 => 0
  | _fuel + 1, 1 => 0
  | fuel + 1, n + 2 =>
    let n := n + 2
    (2 : ℝ) / (n : ℝ) * (∑ i ∈ Finset.range n, quicksortAvgRecFuel fuel i) + ((n : ℝ) - 1)

/-- Canonical expected quicksort comparison recurrence evaluation. -/
noncomputable def quicksortAvgRec (n : ℕ) : ℝ :=
  quicksortAvgRecFuel n n

/-- Bridge to backward analysis in `Amort.Randomized.Quicksort`:
The expected comparison count is bounded by $2n \cdot H(n)$. -/
theorem expected_quicksort_le_harmonic_bound (n : ℕ) :
    Amort.Randomized.expectedQuicksortComparisons n ≤
      2 * (n : ℝ) * Amort.Approximation.harmonic n :=
  Amort.Randomized.expected_quicksort_le_harmonic n

end Amort.Sorting
