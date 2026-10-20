/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Limits

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme

/-- A scheme with finite discrete underlying topological space is affine. -/
theorem isAffine_of_finite_discrete (X : Scheme.{u}) [Finite X] [DiscreteTopology X] :
    IsAffine X := inferInstance

end AlgebraicGeometry.Scheme
