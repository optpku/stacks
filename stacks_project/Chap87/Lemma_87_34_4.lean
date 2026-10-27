/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.EtaleSite.AffineComparison
import StacksCheckRecall

/-! # Affine étale charts of an affine formal algebraic space -/

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 87.34.4: affine formal étale domains over an affine formal algebraic space are
 equivalent to affine étale charts of its reduction. -/
@[stacks 0DEE] #check
  (AlgebraicGeometry.FormalAlgebraicSpace.ReductionData.affineEtaleOverEquiv :
    ∀ {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u)
      [FormalAlgebraicSpace.IsFormalAlgebraicSpace X] (R : FormalAlgebraicSpace.ReductionData X),
      (∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·)) (D : Λ ⥤ Over S),
        FormalAlgebraicSpace.IsDirectedAffineThickeningColimit D X) →
      (AffineFormalAlgebraicSpace.AffineEtaleOver X ≌ AlgebraicSpace.affineEtaleSite R.space))
