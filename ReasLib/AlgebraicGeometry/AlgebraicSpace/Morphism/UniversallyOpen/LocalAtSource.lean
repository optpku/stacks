/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Local
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversallyOpen
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Fppf

/-!
# Universal openness is fppf local on the source

Universally open morphisms of algebraic spaces are local on the source for the
fppf precoverage.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.UniversallyOpen

/-- Universal openness of morphisms of algebraic spaces is local on the source
for the fppf precoverage. -/
instance isLocalAtSourceFppf {S : Scheme.{u}} :
    MorphismProperty.IsLocalAtSource
      (@UniversallyOpen S : MorphismProperty (AlgebraicSpace S))
      (fppfPrecoverage S) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.UniversallyOpen
