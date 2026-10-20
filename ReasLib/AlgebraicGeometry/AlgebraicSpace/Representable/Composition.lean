/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Representable

/-!
# Composition of morphisms representable by algebraic spaces

The property of being representable by algebraic spaces is stable under
composition of maps of presheaves on schemes over `S`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- If `a : F ⟶ G` and `b : G ⟶ H` are representable by algebraic spaces, then
so is the composite `a ≫ b`. -/
theorem representableByAlgebraicSpaces.comp {S : Scheme.{u}}
    {F G H : (Over S)ᵒᵖ ⥤ Type u} (a : F ⟶ G) (b : G ⟶ H)
    (ha : representableByAlgebraicSpaces a) (hb : representableByAlgebraicSpaces b) :
    representableByAlgebraicSpaces (a ≫ b) := sorry

/-- The property of being representable by algebraic spaces is stable under
composition of presheaf morphisms. -/
instance representableByAlgebraicSpaces.isStableUnderComposition {S : Scheme.{u}} :
    IsStableUnderComposition (@representableByAlgebraicSpaces S) where
  comp_mem a b ha hb := representableByAlgebraicSpaces.comp a b ha hb

end AlgebraicGeometry.AlgebraicSpace
