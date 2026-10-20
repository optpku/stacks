/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Regular.Locality

universe u

/- This compatibility module exposes regular scheme morphisms at its historical import path. -/
#check
  (@AlgebraicGeometry.Regular :
    CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
