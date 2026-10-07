module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Cover.V.Standard

@[expose] public section

universe u

/-!
# Lemma 34.10.2

This chapter entry is a compatibility facade for the standard-fpqc-to-standard-
`V` bridge.
-/

/- Lemma 34.10.2: a standard fpqc covering is a standard `V` covering. -/
@[stacks 0ETC] #check
  (AlgebraicGeometry.StandardFpqcCover.isStandardVCover :
    ∀ {T : AlgebraicGeometry.Scheme.{u}}
      (cover : AlgebraicGeometry.StandardFpqcCover T),
        AlgebraicGeometry.AffineFamilyOver.IsStandardVCover
          (AlgebraicGeometry.StandardFpqcCover.toAffineFamily cover))
