/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.EtaleSite.AffineComparison
import StacksCheckRecall

/-!
# Lemma 87.34.7

The affine étale site of the reduction of a formal algebraic space is
equivalent to the category of morphisms of formal algebraic spaces whose
domain is affine and which are representable by algebraic spaces and étale.
-/

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 87.34.7: affine formal domains representably étale over a formal algebraic space
are equivalent to affine étale charts of its reduction. -/
@[stacks 0DEH] #check
  (AlgebraicGeometry.FormalAlgebraicSpace.ReductionData.affineEtaleEquiv :
    ∀ {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u}
      [AlgebraicGeometry.FormalAlgebraicSpace.IsFormalAlgebraicSpace X]
      (R : AlgebraicGeometry.FormalAlgebraicSpace.ReductionData X),
      AlgebraicGeometry.AffineFormalAlgebraicSpace.AffineEtaleOver X ≌
        AlgebraicGeometry.AlgebraicSpace.affineEtaleSite R.space)
