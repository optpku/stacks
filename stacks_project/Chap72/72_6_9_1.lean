/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.ClassGroup
import StacksCheckRecall

open AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

universe u

section

variable {S : Scheme.{u}} (X : AlgebraicSpace S)
variable [IsLocallyNoetherian X] [IsIntegral X]

/- 72.6.9.1: Writing `R(X)ˣ` for `(RationalFunction X)ˣ`, `Div(X)` for
`WeilDivisor X`, and `Cl(X)` for `WeilDivisorClassGroup X`, the maps
`principalWeilDivisor` (`div`) and `weilDivisorClassGroupMk` present `Cl(X)` by
the exact complex `R(X)ˣ → Div(X) → Cl(X) → 0`. -/
@[stacks 0ENS] #check
  (AlgebraicGeometry.AlgebraicSpace.weilDivisorClass_exactSequence X :
    Function.Exact (principalWeilDivisor X) (weilDivisorClassGroupMk X) ∧
      Function.Surjective (weilDivisorClassGroupMk X))

end
