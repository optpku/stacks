/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap101.Definition_101_38_1_SchemeTheoreticImage

/-!
# Functoriality of scheme-theoretic images of algebraic stacks

A commutative square of algebraic stacks induces a 1-morphism between
scheme-theoretic images of the horizontal maps. There is no chosen image
carrier: the comparison is stated at the existence/universal-property layer.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Groupoids.Hom
open scoped Bicategory

namespace AlgebraicGeometry.AlgebraicStack

namespace IsSchemeTheoreticImage

/-- A commutative square of algebraic stacks induces a 1-morphism between
scheme-theoretic images of the horizontal maps, filling both output squares. -/
theorem exists_imageMap {S : Scheme.{u}}
    {X1 X2 Y1 Y2 Z1 Z2 : GroupoidsOver S}
    [AlgebraicStack X1] [AlgebraicStack X2]
    [AlgebraicStack Y1] [AlgebraicStack Y2]
    [AlgebraicStack Z1] [AlgebraicStack Z2]
    {f₁ : X1 ⟶ Y1} {f₂ : X2 ⟶ Y2} {gX : X1 ⟶ X2} {gY : Y1 ⟶ Y2}
    {toImage₁ : X1 ⟶ Z1} {ι₁ : Z1 ⟶ Y1}
    {toImage₂ : X2 ⟶ Z2} {ι₂ : Z2 ⟶ Y2}
    (sq : f₁ ≫ gY = gX ≫ f₂)
    [IsSchemeTheoreticImage f₁ toImage₁ ι₁]
    [IsSchemeTheoreticImage f₂ toImage₂ ι₂] :
    ∃ h : Z1 ⟶ Z2, h ≫ ι₂ = ι₁ ≫ gY ∧ gX ≫ toImage₂ = toImage₁ ≫ h := sorry

/-- The 1-morphism of scheme-theoretic images induced by a commutative square
is unique. -/
theorem existsUnique_imageMap {S : Scheme.{u}}
    {X1 X2 Y1 Y2 Z1 Z2 : GroupoidsOver S}
    [AlgebraicStack X1] [AlgebraicStack X2]
    [AlgebraicStack Y1] [AlgebraicStack Y2]
    [AlgebraicStack Z1] [AlgebraicStack Z2]
    {f₁ : X1 ⟶ Y1} {f₂ : X2 ⟶ Y2} {gX : X1 ⟶ X2} {gY : Y1 ⟶ Y2}
    {toImage₁ : X1 ⟶ Z1} {ι₁ : Z1 ⟶ Y1}
    {toImage₂ : X2 ⟶ Z2} {ι₂ : Z2 ⟶ Y2}
    (sq : f₁ ≫ gY = gX ≫ f₂)
    [IsSchemeTheoreticImage f₁ toImage₁ ι₁]
    [IsSchemeTheoreticImage f₂ toImage₂ ι₂] :
    ∃! h : Z1 ⟶ Z2, h ≫ ι₂ = ι₁ ≫ gY ∧ gX ≫ toImage₂ = toImage₁ ≫ h := sorry

end IsSchemeTheoreticImage

end AlgebraicGeometry.AlgebraicStack
