/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Tutorial.BinaryGCD
import Tutorial.EuclideanGCD
import Tutorial.InsertionSort
import Tutorial.BinarySearch
import Tutorial.DynamicArray
import Tutorial.ModExp

/-!
# Tutorial Companion Library

This library provides interactive Lean 4 companion files for the Verified Algorithms
Skill Tree tutorial curriculum.

Each module exposes verified algorithms from `Amort`, runnable `#eval` examples,
coupling theorems between algorithms and instrumented counters, and hands-on exercises
demonstrating both genuine theorems and common fake specifications.

## Modules
- `Tutorial.BinaryGCD`: Stein's algorithm, parity steps, bit-length logarithmic bounds.
- `Tutorial.EuclideanGCD`: Euclidean algorithm, modulo halving, cross-algorithm equivalence.
- `Tutorial.InsertionSort`: Sorting specifications (`List.Perm` + `List.Pairwise`),
  comparison bounds, fake specifications.
- `Tutorial.BinarySearch`: `Option` results, sortedness as a precondition, probe counting.
- `Tutorial.DynamicArray`: Capacity doubling, the potential method, total cost of `k` pushes.
- `Tutorial.ModExp`: Repeated squaring, modular arithmetic, the condition on the modulus.
-/
