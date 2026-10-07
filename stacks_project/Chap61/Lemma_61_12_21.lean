module

import stacks_project.Chap61.Lemma_61_12_21_AffineIndEtale
import stacks_project.Chap61.Lemma_61_12_21_Comparison
import StacksCheckRecall

open CategoryTheory
open AlgebraicGeometry

universe u

/- Lemma 61.12.21: for an affine scheme `S`, the full subcategory of affine
objects `U` of the small pro-étale site such that `Γ(S, ⊤) ⟶ Γ(U, ⊤)` is
ind-étale, with standard pro-étale coverings, has the property that
restriction of sheaves along the inclusion is an equivalence of topoi. -/
@[stacks 098X] #check
  (AlgebraicGeometry.Scheme.ProEt.AffineIndEtaleComparison.restrictionIsEquivalence :
    ∀ (S : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsAffine S],
      Functor.IsEquivalence
        (AlgebraicGeometry.Scheme.ProEt.affineIndEtaleRestriction S))

#check AlgebraicGeometry.Scheme.ProEt.AffineIndEtale

#check AlgebraicGeometry.Scheme.ProEt.affineIndEtaleInclusion

#check AlgebraicGeometry.Scheme.ProEt.AffineIndEtaleComparison.isSpecialCocontinuous
