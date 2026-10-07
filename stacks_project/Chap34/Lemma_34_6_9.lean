module

import ReasLib.AlgebraicGeometry.Scheme.Sites.Syntomic.AffineComparison
import StacksCheckRecall

open CategoryTheory

universe u

variable (S : AlgebraicGeometry.Scheme.{u})

/-
Lemma 34.6.9 (1): the inclusion `(Aff/S)_{syntomic} ⥤ (Sch/S)_{syntomic}` is special
cocontinuous.
-/
@[stacks 06VD] #check
  (AlgebraicGeometry.Scheme.Syntomic.AffineComparison.isSpecialCocontinuous S :
    CategoryTheory.Functor.IsSpecialCocontinuous
      (AlgebraicGeometry.Scheme.AffineOver.forget S)
      (AlgebraicGeometry.Scheme.Syntomic.StandardAffine.topology S)
      (AlgebraicGeometry.Scheme.syntomicOverTopology S))

/-
Lemma 34.6.9 (2): the cocontinuous direct image from affine syntomic sheaves to big syntomic
sheaves is an equivalence.
-/
@[stacks 06VD] #check
  (AlgebraicGeometry.Scheme.Syntomic.AffineComparison.directImageIsEquivalence S :
    CategoryTheory.Functor.IsEquivalence
      ((AlgebraicGeometry.Scheme.AffineOver.forget S).sheafPushforwardCocontinuous
        (Type (u + 1))
        (AlgebraicGeometry.Scheme.Syntomic.StandardAffine.topology S)
        (AlgebraicGeometry.Scheme.syntomicOverTopology S)))
