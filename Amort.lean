/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Amort.GCD.BinaryGCD
import Amort.GCD.StepCount
import Amort.GCD.EuclideanGCD
import Amort.GCD.Asymptotics

/-!
# Amort: Formalized Algorithm Complexity in Lean 4

This library formalizes the time complexity and mathematical correctness of classical
algorithms and amortized data structures.

## Modules
- `Amort.GCD.BinaryGCD`: Definition, invariant lemmas, and proof of equivalence
  for Stein's Binary GCD.
- `Amort.GCD.StepCount`: Step counting, instrumented representation, and bit-length
  logarithmic bounds for Binary GCD.
- `Amort.GCD.EuclideanGCD`: Step counting and logarithmic upper bounds for the
  standard Euclidean algorithm via modulo halving.
- `Amort.GCD.Asymptotics`: Bridges connecting concrete step bounds to Mathlib's
  `Asymptotics.IsBigO` framework.
-/
