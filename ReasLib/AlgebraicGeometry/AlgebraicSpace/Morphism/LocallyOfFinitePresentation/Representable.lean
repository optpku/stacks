/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation

/-! # Locally finitely presented morphisms of represented algebraic spaces -/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A locally finitely presented morphism of schemes over the base induces a locally
finitely presented morphism of algebraic spaces. -/
instance instLocallyOfFinitePresentation_ofOverMap {S : Scheme.{u}} {U V : Over S}
    (h : U ⟶ V) [AlgebraicGeometry.LocallyOfFinitePresentation h.left] :
    LocallyOfFinitePresentation (ofOverMap h) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
