module

public import stacks_project.Chap101.Lemma_101_38_4_SchemeTheoreticImage
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

/- Lemma 101.38.4: Let `S` be a scheme. A commutative square of algebraic stacks
over `S` induces a morphism between the scheme-theoretic images of the
horizontal maps, filling the two squares `X₁ ⟶ Z₁ ⟶ Y₁` over `X₂ ⟶ Z₂ ⟶ Y₂`. -/
@[stacks 0CPV] #check
  (@AlgebraicGeometry.AlgebraicStack.IsSchemeTheoreticImage.exists_imageMap :
    ∀ {S : Scheme.{u}} {X1 X2 Y1 Y2 Z1 Z2 : GroupoidsOver S}
      [AlgebraicStack X1] [AlgebraicStack X2]
      [AlgebraicStack Y1] [AlgebraicStack Y2]
      [AlgebraicStack Z1] [AlgebraicStack Z2]
      {f₁ : X1 ⟶ Y1} {f₂ : X2 ⟶ Y2} {gX : X1 ⟶ X2} {gY : Y1 ⟶ Y2}
      {toImage₁ : X1 ⟶ Z1} {ι₁ : Z1 ⟶ Y1}
      {toImage₂ : X2 ⟶ Z2} {ι₂ : Z2 ⟶ Y2},
      f₁ ≫ gY = gX ≫ f₂ →
        ∀ [AlgebraicGeometry.AlgebraicStack.IsSchemeTheoreticImage f₁ toImage₁ ι₁]
          [AlgebraicGeometry.AlgebraicStack.IsSchemeTheoreticImage f₂ toImage₂ ι₂],
          ∃ h : Z1 ⟶ Z2, h ≫ ι₂ = ι₁ ≫ gY ∧ gX ≫ toImage₂ = toImage₁ ≫ h)
