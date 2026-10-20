/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Complement

universe u

/- Lemma 31.13.4 (1): if `D ⊆ S` is an effective Cartier divisor and
`U = S \ D`, then the open immersion `U ⟶ S` is an affine morphism. -/
@[stacks 07ZU] #check
  (AlgebraicGeometry.IsEffectiveCartierDivisor.isAffineHom_closedImmersionComplement :
    ∀ {S D : AlgebraicGeometry.Scheme.{u}} (i : D ⟶ S)
      [AlgebraicGeometry.IsEffectiveCartierDivisor i],
      AlgebraicGeometry.IsAffineHom (AlgebraicGeometry.closedImmersionComplement i).ι)

/- Lemma 31.13.4 (2): if `D ⊆ S` is an effective Cartier divisor and
`U = S \ D`, then `U` is scheme theoretically dense in `S`. -/
@[stacks 07ZU] #check
  (AlgebraicGeometry.IsEffectiveCartierDivisor.schemeTheoreticallyDense_closedImmersionComplement :
    ∀ {S D : AlgebraicGeometry.Scheme.{u}} (i : D ⟶ S)
      [AlgebraicGeometry.IsEffectiveCartierDivisor i],
      AlgebraicGeometry.schemeTheoreticallyDense
        (AlgebraicGeometry.closedImmersionComplement i))
