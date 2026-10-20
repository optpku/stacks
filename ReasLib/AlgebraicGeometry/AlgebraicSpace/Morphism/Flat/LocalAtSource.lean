/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Local
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sites.FpqcPrecoverage

/-!
# Fpqc source-locality of flat morphisms of algebraic spaces

Flatness of morphisms of algebraic spaces is local on the source for the fpqc
precoverage.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Flat

/-- Flatness of morphisms of algebraic spaces is local on the source for the
fpqc precoverage. -/
instance isLocalAtSourceFpqc {S : Scheme.{u}} :
    MorphismProperty.IsLocalAtSource
      (@Flat S : MorphismProperty (AlgebraicSpace S))
      (fpqcPrecoverage S) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Flat
