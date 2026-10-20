/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Gluing.DoubleAlong.AffinePlaneChartPullback
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.DoubledOrigin

universe u

variable (k : Type u) [Field k]

/- Each source is the affine plane `affineSpace k 2`, which is affine. -/
#check (inferInstance : IsAffine (affineSpace k 2))

/- The chosen fibre product of the two affine-plane charts of affine 2-space
with doubled origin. -/
#check
  (AlgebraicGeometry.DoubledOrigin.affinePlaneChartPullback k : Scheme.{u})

/- Exercise 111.33.14: both sources are affine planes, while their indicated
fibre product over the doubled-origin scheme is not affine. -/
@[stacks 0290] #check
  (AlgebraicGeometry.DoubledOrigin.not_isAffine_affinePlaneChartPullback k :
    ¬ IsAffine (AlgebraicGeometry.DoubledOrigin.affinePlaneChartPullback k))
