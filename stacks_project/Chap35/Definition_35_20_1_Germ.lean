/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Germ

@[expose] public section

/- Compatibility check for constructing a scheme germ from a scheme and a point. -/
#check (AlgebraicGeometry.Scheme.Germ.of :
  (X : AlgebraicGeometry.Scheme) → X → AlgebraicGeometry.Scheme.Germ)
