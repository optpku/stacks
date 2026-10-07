module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Cover.StandardEtale

@[expose] public section

universe u

/-!
# Definition 34.4.5

This chapter entry is a compatibility facade for finite standard étale chart
covers.
-/

/- Definition 34.4.5: a standard étale covering of an affine scheme is a finite
family of affine étale maps whose images cover the target. -/
@[stacks 0219] #check
  (AlgebraicGeometry.StandardEtaleCover :
    ∀ (T : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsAffine T], Type (u + 1))
