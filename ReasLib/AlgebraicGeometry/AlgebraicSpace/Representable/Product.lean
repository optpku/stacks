/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Representable.Composition

/-!
# Products of morphisms representable by algebraic spaces

The property of being representable by algebraic spaces is stable under
binary products of maps of presheaves on schemes over `S`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The product of two morphisms of presheaves on schemes over a scheme that are
representable by algebraic spaces is representable by algebraic spaces. -/
theorem representableByAlgebraicSpaces.prod_map {S : Scheme.{u}}
    {F₁ F₂ G₁ G₂ : (Over S)ᵒᵖ ⥤ Type u} (a₁ : F₁ ⟶ G₁) (a₂ : F₂ ⟶ G₂)
    (ha₁ : representableByAlgebraicSpaces a₁) (ha₂ : representableByAlgebraicSpaces a₂) :
    representableByAlgebraicSpaces (prod.map a₁ a₂) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
