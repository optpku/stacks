/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.QuadricCone

universe u

/- The affine quadratic cone as a scheme over its coefficient field. -/
#check (AlgebraicGeometry.QuadricCone.overField :
  ∀ (k : Type u) [Field k], AlgebraicGeometry.SchemeOverField k)
