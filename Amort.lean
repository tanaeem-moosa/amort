/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Amort.Basic
import Amort.BinaryGCD
import Amort.StepCount

/-!
# Amort: Binary GCD (Stein's Algorithm) Formalization in Lean 4

This library formalizes Stein's binary GCD algorithm in Lean 4, proves its termination,
demonstrates exact mathematical equivalence with `Nat.gcd`, and establishes logarithmic
step complexity bounds in terms of bit length.
-/
