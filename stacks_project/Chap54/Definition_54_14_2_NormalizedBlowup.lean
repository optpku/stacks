/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Normalized

universe u

/- Normalized point blowups retain their explicit ordinary blowup and normalization data. -/
#check (AlgebraicGeometry.Scheme.NormalizedBlowup :
  AlgebraicGeometry.Scheme.{u} → Type (u + 1))
