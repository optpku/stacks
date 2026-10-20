/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Shift
import StacksCheckRecall

universe u v

/- Definition 22.4.3 [09JL]: the integer shift of a right differential graded module is
canonically represented by `DifferentialGradedModule.shift`. -/
@[stacks 09JL] #check
  (@DifferentialGradedModule.shift.{u, v} :
    {R : Type u} → [CommRing R] → {A : CochainDGAlgebra R} →
      DifferentialGradedModule.{u, max v u} A → ℤ →
        DifferentialGradedModule.{u, max v u} A)
