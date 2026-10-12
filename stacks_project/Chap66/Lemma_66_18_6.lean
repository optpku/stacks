/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Lemma_66_18_6_Site

/-!
# Comparison of the affine étale site with the small étale site

The inclusion of affine objects in the small étale site of an algebraic space is special
cocontinuous. Its cocontinuous direct image therefore induces an equivalence on sheaves of
sets.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 66.18.6 (1): the functor `affineEtaleSite X ⥤ smallEtaleSite X` sending an affine
scheme étale over `X` to the same object is special cocontinuous. -/
@[stacks 04JS]
instance affineEtaleInclusion_isSpecialCocontinuous {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (affineEtaleInclusion X).IsSpecialCocontinuous (affineEtaleTopology X)
      (smallEtaleTopology X) :=
  sorry

/-- Lemma 66.18.6 (2): the cocontinuous direct image along `affineEtaleInclusion X` is an
equivalence `Sheaf (affineEtaleTopology X) ⥤ Sheaf (smallEtaleTopology X)` on sheaves of sets. -/
@[stacks 04JS]
instance affineEtaleInclusion_directImage_isEquivalence {S : Scheme.{u}} (X : AlgebraicSpace S) :
    ((affineEtaleInclusion X).sheafPushforwardCocontinuous (Type (u + 1))
      (affineEtaleTopology X) (smallEtaleTopology X)).IsEquivalence :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
