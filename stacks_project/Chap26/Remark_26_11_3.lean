/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Gluing.DoubleAlong.AffineSpace
import StacksCheckRecall

@[expose] public section

/- Remark 26.11.3: two affine opens can have non-affine intersection. -/
@[stacks 01IU] #check
  AlgebraicGeometry.DoubledOrigin.chart_inf_not_isAffineOpen
#check AlgebraicGeometry.DoubledOrigin.chart_isAffineOpen
