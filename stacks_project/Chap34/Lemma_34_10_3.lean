/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Cover.V.Standard

@[expose] public section

universe u

/-!
# Lemma 34.10.3

This chapter entry is a compatibility facade for the standard proper-
surjective-to-standard-`V` bridge.
-/

/- Lemma 34.10.3: A standard ph covering is a standard V covering. -/
@[stacks 0ETD] #check
  (AlgebraicGeometry.StandardPhCovering.isStandardVCover :
    ∀ {T : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsAffine T]
      (cover : AlgebraicGeometry.StandardPhCovering T),
      AlgebraicGeometry.AffineFamilyOver.IsStandardVCover
        (AlgebraicGeometry.StandardPhCovering.toAffineFamily cover))
