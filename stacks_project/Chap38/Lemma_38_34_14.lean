/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.H.ChosenPresentation.Affine
import StacksCheckRecall

universe u v

/- Lemma 38.34.14: for a scheme `S` in a chosen big h site, the finite
h-covering families between affine objects over `S` form a site. -/
@[stacks 0EU2] #check
  (AlgebraicGeometry.ChosenBigHSite.bigAffinePretopology :
    (X : AlgebraicGeometry.ChosenBigHSite.{u, v}) →
      (S : X.carrier) →
        @CategoryTheory.Pretopology
          (AlgebraicGeometry.ChosenBigSite.affineSite X S) _
          (AlgebraicGeometry.ChosenBigSite.affineSiteHasPullbacks X S))
