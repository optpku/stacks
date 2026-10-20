/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.DualNumber
public import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.Tactic.CrossRefAttribute

/-!
# The canonical basis of the dual numbers

The standard `Fin 2` basis of the dual numbers consists of `1` and `ε`.
-/

@[expose] public section

open scoped DualNumber

universe u

section

variable (R : Type u) [CommRing R]

namespace DualNumber

/-- The canonical `Fin 2` basis of `R[ε]` consists, in order, of `1` and `ε`. -/
@[stacks 0B29]
theorem finTwoProd_eq_one_eps :
    Module.Basis.finTwoProd R 0 = (1 : R[ε]) ∧
      Module.Basis.finTwoProd R 1 = (ε : R[ε]) := by
  constructor
  · rw [Module.Basis.finTwoProd_zero]
    rfl
  · rw [Module.Basis.finTwoProd_one]
    rfl

end DualNumber

end
