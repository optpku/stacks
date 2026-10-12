/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.OverField.CompleteIntersection
import StacksCheckRecall

universe u

/- Lemma 29.30.9: for a scheme locally of finite type over a field, being a local complete
intersection, having affine global-complete-intersection neighborhoods, and having
complete-intersection stalks over the field are equivalent. -/
@[stacks 01UG] #check
  (AlgebraicGeometry.SchemeOverField.localCompleteIntersection_tfae :
    ∀ {k : Type u} [Field k]
      (X : AlgebraicGeometry.SchemeOverField k)
      [AlgebraicGeometry.LocallyOfFiniteType X.hom],
      List.TFAE
        [ AlgebraicGeometry.IsLocalCompleteIntersectionOver k X.hom
        , AlgebraicGeometry.SchemeOverField.HasAffineGlobalCompleteIntersectionNeighborhoods X
        , AlgebraicGeometry.SchemeOverField.HasCompleteIntersectionStalks X
        ])
