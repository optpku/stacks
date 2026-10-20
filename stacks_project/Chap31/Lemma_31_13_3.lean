/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.LocallyPrincipal.Complement
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier

universe u

/- Lemma 31.13.3: if `i : Z ⟶ S` is a locally principal closed subscheme of a scheme `S`,
then the inclusion of the open complement of its image into `S` is an affine morphism. -/
@[stacks 07ZT] #check
  (AlgebraicGeometry.IsLocallyPrincipalClosedSubscheme.isAffineHom_closedImmersionComplement :
    ∀ {S Z : AlgebraicGeometry.Scheme.{u}} (i : Z ⟶ S)
      [AlgebraicGeometry.IsLocallyPrincipalClosedSubscheme i],
      AlgebraicGeometry.IsAffineHom (AlgebraicGeometry.closedImmersionComplement i).ι)
