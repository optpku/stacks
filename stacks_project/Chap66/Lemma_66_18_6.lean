/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Comparison
public import stacks_project.Chap66.Lemma_66_18_6_Site
import StacksCheckRecall

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

variable {S : Scheme.{u}} (X : AlgebraicGeometry.AlgebraicSpace S)

/- Lemma 66.18.6 (1): the functor `affineEtaleSite X ⥤ smallEtaleSite X` sending an affine
scheme étale over `X` to the same object is special cocontinuous. -/
@[stacks 04JS] #check
  (AlgebraicGeometry.AlgebraicSpace.affineEtaleInclusion_isSpecialCocontinuous X :
    (AlgebraicGeometry.AlgebraicSpace.affineEtaleInclusion X).IsSpecialCocontinuous
      (AlgebraicGeometry.AlgebraicSpace.affineEtaleTopology X)
      (AlgebraicGeometry.AlgebraicSpace.smallEtaleTopology X))

/- Lemma 66.18.6 (2): the cocontinuous direct image along `affineEtaleInclusion X` is an
equivalence `Sheaf (affineEtaleTopology X) ⥤ Sheaf (smallEtaleTopology X)` on sheaves of sets. -/
@[stacks 04JS] #check
  (AlgebraicGeometry.AlgebraicSpace.affineEtaleInclusion_directImage_isEquivalence X :
    ((AlgebraicGeometry.AlgebraicSpace.affineEtaleInclusion X).sheafPushforwardCocontinuous
      (Type (u + 1)) (AlgebraicGeometry.AlgebraicSpace.affineEtaleTopology X)
      (AlgebraicGeometry.AlgebraicSpace.smallEtaleTopology X)).IsEquivalence)
