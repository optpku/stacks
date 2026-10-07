module

import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.Comparison
import StacksCheckRecall

open CategoryTheory
open AlgebraicGeometry

universe u

/- Lemma 61.12.20: the full subcategory of affine objects of the small
pro-étale site, with standard pro-étale coverings, has the property that
restriction of sheaves along the inclusion is an equivalence of topoi. -/
@[stacks 098W] #check
  (AlgebraicGeometry.Scheme.ProEt.SmallAffineComparison.restrictionIsEquivalence :
    ∀ S : AlgebraicGeometry.Scheme.{u}, Functor.IsEquivalence
      (AlgebraicGeometry.Scheme.ProEt.affineRestriction S))
