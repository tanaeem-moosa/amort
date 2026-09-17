/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Amort.GCD.BinaryGCD
import Amort.GCD.StepCount
import Amort.GCD.EuclideanGCD
import Amort.GCD.Asymptotics
import Amort.Sorting.InsertionSort
import Amort.Sorting.MergeSort
import Amort.Sorting.Asymptotics
import Amort.Sorting.DecisionTree
import Amort.Sorting.LowerBound
import Amort.Recurrence.Composition
import Amort.Recurrence.Telescoping
import Amort.Recurrence.Halving
import Amort.Recurrence.BinarySearch
import Amort.Recurrence.MasterTheorem
import Amort.String.NaiveMatch
import Amort.String.KMP
import Amort.String.LCS
import Amort.String.EditDistance
import Amort.String.Asymptotics

/-!
# Amort: Formalized Algorithm Complexity in Lean 4

This library formalizes the time complexity and mathematical correctness of classical
algorithms, recurrence relations, and amortized data structures.

## Modules
- `Amort.GCD.BinaryGCD`: Definition, invariant lemmas, and proof of equivalence
  for Stein's Binary GCD.
- `Amort.GCD.StepCount`: Step counting, instrumented representation, and bit-length
  logarithmic bounds for Binary GCD.
- `Amort.GCD.EuclideanGCD`: Step counting and logarithmic upper bounds for the
  standard Euclidean algorithm via modulo halving.
- `Amort.GCD.Asymptotics`: Bridges connecting concrete step bounds to Mathlib's
  `Asymptotics.IsBigO` framework.
- `Amort.Sorting.InsertionSort`: Comparison counting, instrumented representation, and
  concrete $O(n^2)$ comparison bounds for Insertion Sort.
- `Amort.Sorting.MergeSort`: Comparison counting, instrumented representation, divide-and-conquer
  recurrence bounds, and concrete $O(n \log n)$ bounds for Merge Sort.
- `Amort.Sorting.Asymptotics`: Bridges connecting concrete sorting comparison bounds to Mathlib's
  `Asymptotics.IsBigO` framework.
- `Amort.Sorting.DecisionTree`: Abstract binary decision tree model, depth, leaf count,
  structural induction bound `leafCount T ≤ 2 ^ depth T`, and tree evaluation.
- `Amort.Sorting.LowerBound`: Permutation coverage, factorial bound $n! \le 2^{\text{depth}}$,
  worst-case depth lower bound $\text{clog}_2(n!) \le \text{depth}$, combinatorial factorial
  growth bound, and asymptotic lower bound $\log(n!) = \Omega(n \log n)$ in Mathlib `IsBigO`.
- `Amort.Recurrence.Composition`: Compositional complexity algebra (nested loop products,
  sequential phase sums, maximum phase bounds, and phase dominance) in Mathlib `IsBigO`.
- `Amort.Recurrence.Telescoping`:
  Linear and power telescoping recurrences ($T(n+1) \le T(n) + f(n)$),
  constant and power step bounds ($O(n^{k+1})$), and connection to Insertion Sort ($O(n^2)$).
- `Amort.Recurrence.Halving`: Halving recurrence ($T(n) \le T(n/2) + c$), bit-length bound
  $T(n) \le c \cdot \text{size } n + T(1)$, and logarithmic asymptotics ($O(\log n)$).
- `Amort.Recurrence.BinarySearch`: Representative binary search comparison counting,
  halving recurrence verification, and $O(\log n)$ complexity proofs.
- `Amort.Recurrence.MasterTheorem`: Balanced divide-and-conquer master recurrence with integer
  rounding ($T(n) \le T(\lceil n/2 \rceil) + T(\lfloor n/2 \rfloor) + c \cdot n$), $O(n \log n)$
  asymptotics, and connection to Merge Sort.
- `Amort.String.NaiveMatch`: Naive sliding-window string matching, character comparison counting,
  concrete worst-case comparison bound $\le (n - m + 1) \cdot m \le n \cdot m$, and substring
  occurrence correctness.
- `Amort.String.KMP`: Knuth-Morris-Pratt string matching, failure function $\pi$, preprocessing
  bound $\le 2m$, potential function analysis on index $j$ proving scanning bound $\le 2n$,
  combined linear bound $\le 2(n + m)$, and equivalence to naive matching.
- `Amort.String.LCS`: Longest Common Subsequence recursive formulation, constructive maximal
  common subsequence witness, bottom-up $(n + 1) \times (m + 1)$ dynamic programming table,
  and concrete operational step bound $\le (n + 1) \cdot (m + 1)$ ($O(n \cdot m)$).
- `Amort.String.EditDistance`: Levenshtein edit distance recursive formulation, explicit alignment
  operations, minimal-cost alignment correctness proof, bottom-up $(n + 1) \times (m + 1)$
  dynamic programming matrix, and concrete step bound $\le (n + 1) \cdot (m + 1)$ ($O(n \cdot m)$).
- `Amort.String.Asymptotics`: Bridges connecting concrete 2D table bounds to
  `Amort.Recurrence.Composition` (`isBigO_nested_loops_nat`), linear KMP bounds to
  `isBigO_sequential_add_nat`, and proving formal $O(n \cdot m)$ and $O(n + m)$ `IsBigO` bounds
  under `Filter.atTop` on $\mathbb{N} \times \mathbb{N}$.
-/
