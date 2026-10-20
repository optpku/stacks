/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.AffineIndEtaleClosedImmersion

@[expose] public section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.ProEt
universe u
variable {X Z : Scheme.{u}} [IsAffine X] [IsAffine Z] (i : Z ⟶ X) [IsClosedImmersion i]

/- Lemma 61.25.1: the affine ind-étale lift preserves coverings. -/
@[stacks 09BK] #check
  (AlgebraicGeometry.Scheme.ProEt.AffineIndEtale.lift_coverPreserving i :
    CoverPreserving (affineIndEtaleTopology Z) (affineIndEtaleTopology X)
      (AffineIndEtale.lift i))
