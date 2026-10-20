/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.SerreCondition.Normal
import StacksCheckRecall

universe u

/- Lemma 31.15.6: let `X` be a locally Noetherian normal scheme and let `D ⊆ X` be an
effective Cartier divisor. Then `D` satisfies Serre's condition `(S₁)`. -/
@[stacks 0B3S] #check
  (AlgebraicGeometry.Scheme.subscheme_satisfiesSerreConditionS_one_of_isNormal :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian X]
      (D : X.IdealSheafData) [AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι]
      (_ : X.isNormal),
      D.subscheme.satisfiesSerreConditionS 1)
