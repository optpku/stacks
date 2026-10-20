/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Cover.StandardSmooth

@[expose] public section

/-!
# Definition 34.5.5

This chapter entry is a compatibility facade for the reusable finite affine
standard-smooth cover presentation.
-/

universe u

/- Definition 34.5.5: the source-facing owner is
`AlgebraicGeometry.StandardSmoothCovering`; its induced ordinary smooth cover
is exposed by `StandardSmoothCovering.smoothCovering`. -/
@[stacks 0223] #check
  (AlgebraicGeometry.StandardSmoothCovering.{u} :
    ∀ (T : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsAffine T], Type (u + 1))
#check AlgebraicGeometry.StandardSmoothCovering.smoothCovering
