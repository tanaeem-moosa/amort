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
import Amort.Sorting.Quicksort
import Amort.Sorting.DecisionTree
import Amort.Sorting.LowerBound
import Amort.DataStructure.DynamicArray
import Amort.DataStructure.TwoStackQueue
import Amort.Recurrence.Telescoping
import Amort.Recurrence.Halving
import Amort.Recurrence.MasterTheorem
import Amort.Recurrence.BinarySearch
import Amort.String.NaiveMatch
import Amort.String.KMP
import Amort.String.LCS
import Amort.String.EditDistance
import Amort.String.Asymptotics
import Amort.DP.Knapsack
import Amort.DP.LIS
import Amort.Greedy.IntervalScheduling
import Amort.Greedy.Asymptotics
import Amort.NumberTheory.ModExp
import Amort.NumberTheory.ExtendedGCD
import Amort.NumberTheory.Asymptotics
import Amort.Graph.BellmanFord
import Amort.Graph.Traversal
import Amort.Graph.Asymptotics
import Amort.Complexity.KarpReductions
import Amort.Complexity.TwoSAT

/-!
# Phase 0 & Definition of Done Axiom Audit

This module validates that all headline theorems across the formalization repository
depend exclusively on foundational Lean 4 axioms (`propext`, `Classical.choice`, `Quot.sound`)
and contain zero instances of `sorryAx` or non-standard axioms.

## Audited Modules
1. **GCD**: Binary GCD and Euclidean GCD (`Nat.binaryGcd_eq_gcd`, `Nat.euclidGcd_eq_gcd`, etc.).
2. **Sorting**: Insertion Sort, Merge Sort, Quicksort, Decision Trees, Lower Bound.
3. **Data Structures**: Dynamic Array amortized bounds, Two-Stack Queue FIFO correctness.
4. **Recurrences**: Binary search functional correctness, probe count bounds, master recurrences.
5. **Strings**: Naive Matching, KMP, LCS optimality, Edit Distance minimal alignment.
6. **Dynamic Programming**: 0/1 Knapsack optimality, table-recursion equivalence, LIS.
7. **Greedy**: Interval Scheduling exchange-argument optimality, operational bounds.
8. **Number Theory**: Modular exponentiation, Extended GCD Bézout identity.
9. **Graphs**: Bellman-Ford step bounds, BFS traversal bounds, handshaking lemma.
10. **Complexity**: 3-SAT to Independent Set reduction, 2-SAT characterization.
-/

namespace Amort.Audit

/-! ### 1. GCD Module Axiom Verification -/

#print axioms Nat.binaryGcd_eq_gcd
#print axioms Nat.binaryGcdWithSteps_fst
#print axioms Nat.binaryGcdWithSteps_snd_le_size_add_size
#print axioms Nat.binaryGcdWithSteps_snd_le_two_mul_size_add
#print axioms Nat.euclidGcd_eq_gcd
#print axioms Nat.euclidGcdWithSteps_fst
#print axioms Nat.euclidGcdWithSteps_snd
#print axioms Nat.euclidGcdWithSteps_snd_le_two_mul_size_min
#print axioms Nat.euclidGcdWithSteps_snd_le_two_mul_size_add
#print axioms Nat.isBigO_binaryGcdSteps_atTop
#print axioms Nat.isBigO_euclidGcdWithSteps_snd_atTop

/-! ### 2. Sorting Module Axiom Verification -/

#print axioms List.insertionSortWithCount_fst
#print axioms List.insertionSortWithCount_perm
#print axioms List.insertionSortWithCount_fst_sorted
#print axioms List.insertionSortWithCount_snd_le_triangular
#print axioms List.insertionSortWithCount_snd_le_sq
#print axioms List.isBigO_insertionSortWithCount_snd_atTop
#print axioms List.mergeSortWithCount_fst
#print axioms List.mergeSortWithCount_perm
#print axioms List.mergeSortWithCount_fst_sorted
#print axioms List.mergeSortWithCount_snd_le_mul_size
#print axioms List.isBigO_mergeSortWithCount_snd_atTop
#print axioms Amort.Sorting.quicksort_perm
#print axioms Amort.Sorting.quicksort_sorted
#print axioms Amort.Sorting.quicksortWithCount_fst
#print axioms Amort.Sorting.quicksortWithCount_snd_le_mul
#print axioms Amort.Sorting.quicksortWithCount_replicate_eq_mul
#print axioms Amort.Sorting.isBigO_quicksortWithCount_snd_sq
#print axioms Amort.Sorting.DecisionTree.leafCount_le_two_pow_depth
#print axioms Amort.Sorting.factorial_le_leafCount
#print axioms Amort.Sorting.isTheta_factorial_n_log_n

/-! ### 3. Data Structure Module Axiom Verification -/

#print axioms Amort.DataStructure.pushSeqCost_telescope_initOne
#print axioms Amort.DataStructure.pushSeqCost_initOne_le
#print axioms Amort.DataStructure.TwoStackQueue.pop_fst
#print axioms Amort.DataStructure.TwoStackQueue.pop_snd_toList
#print axioms Amort.DataStructure.TwoStackQueue.pop_spec
#print axioms Amort.DataStructure.totalActualCost_le_three_mul

/-! ### 4. Recurrence & Binary Search Axiom Verification -/

#print axioms Amort.Recurrence.telescoping_linear_step_isBigO_sq
#print axioms Amort.Recurrence.halving_recurrence_bound
#print axioms Amort.Recurrence.master_divide_conquer_isBigO_n_log_n
#print axioms Amort.Recurrence.binarySearch_some_get
#print axioms Amort.Recurrence.binarySearch_isSome_iff
#print axioms Amort.Recurrence.binarySearchWithCount_fst
#print axioms Amort.Recurrence.binarySearchWithCount_snd_le_steps
#print axioms Amort.Recurrence.binarySearchWithCount_snd_le_size
#print axioms Amort.Recurrence.binarySearchArray_isSome_iff
#print axioms Amort.Recurrence.binarySearchArrayWithCount_fst
#print axioms Amort.Recurrence.binarySearchArrayWithCount_snd_le_size
#print axioms Amort.Recurrence.binarySearchSteps_isBigO_size

/-! ### 5. String Algorithms Axiom Verification -/

#print axioms Amort.String.mem_naiveMatch_iff
#print axioms Amort.String.naiveMatchCount_le_mul
#print axioms Amort.String.computePiWithCount_fst
#print axioms Amort.String.computePi_getD
#print axioms Amort.String.computePiWithCount_snd_le
#print axioms Amort.String.mem_kmpMatch_iff
#print axioms Amort.String.kmpWithCount_fst
#print axioms Amort.String.kmpWithCount_snd_le
#print axioms Amort.String.kmpScan_bound
#print axioms Amort.String.kmpScan_le_two_mul
#print axioms Amort.String.isBigO_kmpWithCount_snd_list
#print axioms Amort.String.lcs_is_optimal
#print axioms Amort.String.lcsTable_eval
#print axioms Amort.String.lcsWithCount_fst
#print axioms Amort.String.lcsWithCount_snd_le
#print axioms Amort.String.isBigO_lcsWithCount_snd_list
#print axioms Amort.String.editDist_is_minimal_alignment
#print axioms Amort.String.editDistTable_eval
#print axioms Amort.String.editDistWithCount_fst
#print axioms Amort.String.editDistWithCount_snd_le
#print axioms Amort.String.isBigO_editDistWithCount_snd_list

/-! ### 6. Dynamic Programming Axiom Verification -/

#print axioms Amort.DP.knapsack_is_optimal
#print axioms Amort.DP.knapsackRow_eval
#print axioms Amort.DP.knapsackWithCount_fst
#print axioms Amort.DP.knapsackWithCount_snd
#print axioms Amort.DP.knapsackWithCount_snd_le
#print axioms Amort.DP.lis_is_optimal

/-! ### 7. Greedy & Number Theory Axiom Verification -/

#print axioms Amort.Greedy.greedyIntervalSchedule_optimal
#print axioms Amort.Greedy.intervalSchedule_valid
#print axioms Amort.Greedy.intervalSchedule_optimal
#print axioms Amort.Greedy.intervalScheduleWithCount_fst
#print axioms Amort.Greedy.intervalScheduleWithCount_snd_le_mul
#print axioms Amort.Greedy.isBigO_intervalScheduleWithCount_snd_mul_size
#print axioms Amort.NumberTheory.modExp_correct
#print axioms Amort.NumberTheory.modExpWithCount_fst
#print axioms Amort.NumberTheory.modExpWithCount_snd_le
#print axioms Amort.NumberTheory.isBigO_modExpWithCount_snd_size
#print axioms Amort.NumberTheory.extGCD_bezout
#print axioms Amort.NumberTheory.extGCD_gcd

/-! ### 8. Graph Algorithms Axiom Verification -/

#print axioms Amort.Graph.bellmanFordWithCount_fst
#print axioms Amort.Graph.bellmanFordWithCount_snd
#print axioms Amort.Graph.bellmanFordWithCount_snd_le
#print axioms Amort.Graph.bellmanFord_le_path_weight
#print axioms Amort.Graph.bellmanFord_achieved
#print axioms Amort.Graph.bellmanFord_optimal
#print axioms Amort.Graph.hasNegCycleCheck_iff
#print axioms Amort.Graph.noNegCycle_not_hasReachableNegCycle
#print axioms Amort.Graph.hasReachableNegCycle_not_noNegCycle
#print axioms Amort.Graph.isBigO_bellmanFord_totalRelaxations_atTop
#print axioms Amort.Graph.handshaking_lemma
#print axioms Amort.Graph.bfs_eq_top_iff
#print axioms Amort.Graph.bfs_eq_coe_iff
#print axioms Amort.Graph.bfs_source
#print axioms Amort.Graph.bfs_fuel_exhaustion_le
#print axioms Amort.Graph.bfs_fuel_sufficient
#print axioms Amort.Graph.bfsWork_le
#print axioms Amort.Graph.bfsWithCount_source
#print axioms Amort.Graph.bfsWithCount_walk
#print axioms Amort.Graph.bfsWithCount_fst
#print axioms Amort.Graph.bfsWithCount_snd_le

/-! ### 9. Complexity & Reduction Axiom Verification -/

#print axioms Amort.Complexity.sat3_to_independentSet_correct
#print axioms Amort.Complexity.twoSAT_soundness_and_completeness

end Amort.Audit
