/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Local
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Fppf

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType

/-- Local finite type of morphisms of algebraic spaces is local on the source
for the fppf precoverage. -/
instance isLocalAtSourceFppf {S : Scheme.{u}} :
    MorphismProperty.IsLocalAtSource
      (@LocallyOfFiniteType S : MorphismProperty (AlgebraicSpace S))
      (fppfPrecoverage S) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType
