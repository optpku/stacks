/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Divisor.LocallyPrincipal.Pullback

open CategoryTheory CategoryTheory.Limits

universe u

/- Lemma 31.13.11: the inverse image of a locally principal closed subscheme under an arbitrary
scheme morphism is locally principal. -/
@[stacks 053P] #check
  (AlgebraicGeometry.IsLocallyPrincipalClosedSubscheme.pullback_fst :
    ∀ {S S' Z : AlgebraicGeometry.Scheme.{u}} (f : S' ⟶ S) (i : Z ⟶ S)
      [AlgebraicGeometry.IsLocallyPrincipalClosedSubscheme i],
      AlgebraicGeometry.IsLocallyPrincipalClosedSubscheme (pullback.fst f i))
