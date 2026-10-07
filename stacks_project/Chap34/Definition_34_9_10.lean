module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.StandardFpqc
import StacksCheckRecall

@[expose] public section

universe u

/-!
# Definition 34.9.10

This chapter entry is a compatibility facade for finite standard fpqc chart
covers.
-/

/- Definition 34.9.10: a standard fpqc covering of an affine scheme is a
finite family of affine flat maps whose images jointly cover the target. -/
@[stacks 022F] #check
  (AlgebraicGeometry.StandardFpqcCover.{u} :
    AlgebraicGeometry.Scheme.{u} → Type (u + 1))

#check AlgebraicGeometry.StandardFpqcCover.toOverFamily
#check AlgebraicGeometry.StandardFpqcCover.toFlatCover
#check AlgebraicGeometry.StandardFpqcCover.fpqcCovering
