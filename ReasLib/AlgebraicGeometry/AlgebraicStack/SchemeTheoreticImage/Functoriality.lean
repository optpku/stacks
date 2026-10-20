/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.SchemeTheoreticImage

/-!
# Functoriality of scheme-theoretic images of algebraic stacks

A square commuting up to 2-isomorphism induces a morphism between the
scheme-theoretic images of its horizontal maps.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

namespace AlgebraicGeometry.AlgebraicStack.IsSchemeTheoreticImage

/-- A square of algebraic stacks commuting up to 2-isomorphism induces a morphism
between the scheme-theoretic images of its horizontal maps, making both resulting
squares commute up to 2-isomorphism. -/
theorem exists_imageMap {S : Scheme.{u}}
    {X1 X2 Y1 Y2 Z1 Z2 : GroupoidsOver S}
    [AlgebraicStack X1] [AlgebraicStack X2]
    [AlgebraicStack Y1] [AlgebraicStack Y2]
    [AlgebraicStack Z1] [AlgebraicStack Z2]
    {f₁ : X1 ⟶ Y1} {f₂ : X2 ⟶ Y2} {gX : X1 ⟶ X2} {gY : Y1 ⟶ Y2}
    {toImage₁ : X1 ⟶ Z1} {ι₁ : Z1 ⟶ Y1}
    {toImage₂ : X2 ⟶ Z2} {ι₂ : Z2 ⟶ Y2}
    (sq : Nonempty (f₁ ≫ gY ≅ gX ≫ f₂))
    [IsSchemeTheoreticImage f₁ toImage₁ ι₁]
    [IsSchemeTheoreticImage f₂ toImage₂ ι₂] :
    ∃ h : Z1 ⟶ Z2, Nonempty (h ≫ ι₂ ≅ ι₁ ≫ gY) ∧
      Nonempty (gX ≫ toImage₂ ≅ toImage₁ ≫ h) := sorry

end AlgebraicGeometry.AlgebraicStack.IsSchemeTheoreticImage
