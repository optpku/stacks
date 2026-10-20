/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.EtaleSite.Comparison
import StacksCheckRecall

/-! # The étale site of a formal algebraic space -/

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 87.34.6: formal algebraic spaces representably étale over a formal space
are equivalent to algebraic spaces étale over its reduction. -/
@[stacks 0DEG] #check
  (AlgebraicGeometry.FormalAlgebraicSpace.ReductionData.spacesEtaleEquiv :
    ∀ {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u}
      [AlgebraicGeometry.FormalAlgebraicSpace.IsFormalAlgebraicSpace X]
      (R : AlgebraicGeometry.FormalAlgebraicSpace.ReductionData X),
      AlgebraicGeometry.FormalAlgebraicSpace.EtaleOver X ≌
        AlgebraicGeometry.AlgebraicSpace.spacesEtaleSite R.space)
