/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Affine
import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Comparison
import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Spaces
import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Reduction
import StacksCheckRecall

/-!
# Equation 87.34.1.1

The sheaf topoi of the three small étale sites of a formal algebraic space
coincide, as those sites are the corresponding étale sites of its reduction
and the identifications are the algebraic-space comparisons of Properties of
Spaces, Lemmas 66.18.3 and 66.18.6.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FormalAlgebraicSpace

universe u

variable {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u)
  [IsFormalAlgebraicSpace X]

/- 87.34.1.1 (1): identification `Sh(X_étale) = Sh(X_spaces,étale)` of the
(small) étale topos of a formal algebraic space, obtained by applying the
algebraic-space comparison of Properties of Spaces, Lemma 66.18.3, to the
reduction of `X`. -/
@[stacks 0DEB] #check
  (AlgebraicGeometry.AlgebraicSpace.smallEtaleInclusion_directImage_isEquivalence
    (ReductionData.canonical X).space :
    ((AlgebraicGeometry.AlgebraicSpace.smallEtaleInclusion
      (ReductionData.canonical X).space).sheafPushforwardCocontinuous (Type (u + 1))
      (AlgebraicGeometry.AlgebraicSpace.SmallEtale.topology (ReductionData.canonical X).space)
      (AlgebraicGeometry.AlgebraicSpace.spacesEtaleTopology
        (ReductionData.canonical X).space)).IsEquivalence)

/- 87.34.1.1 (2): identification `Sh(X_affine,étale) = Sh(X_étale)` of the
(small) étale topos of a formal algebraic space, obtained by applying the
algebraic-space comparison of Properties of Spaces, Lemma 66.18.6, to the
reduction of `X`. -/
@[stacks 0DEB] #check
  (AlgebraicGeometry.AlgebraicSpace.affineEtaleInclusion_directImage_isEquivalence
    (ReductionData.canonical X).space :
    ((AlgebraicGeometry.AlgebraicSpace.affineEtaleInclusion
      (ReductionData.canonical X).space).sheafPushforwardCocontinuous (Type (u + 1))
      (AlgebraicGeometry.AlgebraicSpace.affineEtaleTopology (ReductionData.canonical X).space)
      (AlgebraicGeometry.AlgebraicSpace.smallEtaleTopology
        (ReductionData.canonical X).space)).IsEquivalence)
