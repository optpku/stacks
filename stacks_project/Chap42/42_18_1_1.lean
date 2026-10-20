/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.ProjectiveSpace.Line.Divisor
import StacksCheckRecall

universe u

/- 42.18.1.1 (1): The distinguished closed subscheme `D₀ ⊂ ProjectiveSpace 1 S` is
the coordinate divisor `V(T₁)`. -/
@[stacks 0F93] #check
  (AlgebraicGeometry.ProjectiveLine.Relative.zeroDivisor :
    (S : AlgebraicGeometry.Scheme.{u}) →
      (AlgebraicGeometry.ProjectiveSpace 1 S).IdealSheafData)

/- 42.18.1.1 (2): The distinguished closed subscheme `D∞ ⊂ ProjectiveSpace 1 S` is
the coordinate divisor `V(T₀)`. -/
@[stacks 0F93] #check
  (AlgebraicGeometry.ProjectiveLine.Relative.infinityDivisor :
    (S : AlgebraicGeometry.Scheme.{u}) →
      (AlgebraicGeometry.ProjectiveSpace 1 S).IdealSheafData)
