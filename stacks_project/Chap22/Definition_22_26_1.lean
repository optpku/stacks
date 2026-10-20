/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.DifferentialGraded
import StacksCheckRecall

universe u v w

variable (R : Type u) [CommRing R]
variable (C : Type v)

/- Definition 22.26.1 [09L5]: a category enriched in differential graded `R`-modules is
canonically represented by `DifferentialGradedCategory`. -/
@[stacks 09L5] #check
  (DifferentialGradedCategory.{u, v, w} R C : Type _)
