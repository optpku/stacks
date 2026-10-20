/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.EffectiveCartier.SerreCondition.Normal
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 71.8.2: Let `S` be a scheme and let `X` be a locally Noetherian normal
algebraic space over `S`. Let `D ⊂ X` be an effective Cartier divisor. Then `D`
is `(S₁)`. -/
@[stacks 0B4H] #check
  (AlgebraicGeometry.AlgebraicSpace.IsEffectiveCartierDivisor.satisfiesSerreConditionS_one :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsLocallyNoetherian X] [IsNormal X]
      (D : ClosedSubspace X) [IsEffectiveCartierDivisor D.ι],
      satisfiesSerreConditionS D.X 1)

end AlgebraicGeometry.AlgebraicSpace
