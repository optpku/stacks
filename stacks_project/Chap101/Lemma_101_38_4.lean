/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.SchemeTheoreticImage.Functoriality
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

/- Lemma 101.38.4: Let `S` be a scheme. A 2-commutative square of algebraic stacks
over `S` induces a morphism between the scheme-theoretic images of the
horizontal maps, filling the two squares `X₁ ⟶ Z₁ ⟶ Y₁` over `X₂ ⟶ Z₂ ⟶ Y₂`. -/
@[stacks 0CPV] #check
  (AlgebraicGeometry.AlgebraicStack.IsSchemeTheoreticImage.exists_imageMap :
    ∀ {S : Scheme.{u}} {X1 X2 Y1 Y2 Z1 Z2 : GroupoidsOver S}
      [AlgebraicStack X1] [AlgebraicStack X2]
      [AlgebraicStack Y1] [AlgebraicStack Y2]
      [AlgebraicStack Z1] [AlgebraicStack Z2]
      {f₁ : X1 ⟶ Y1} {f₂ : X2 ⟶ Y2} {gX : X1 ⟶ X2} {gY : Y1 ⟶ Y2}
      {toImage₁ : X1 ⟶ Z1} {ι₁ : Z1 ⟶ Y1}
      {toImage₂ : X2 ⟶ Z2} {ι₂ : Z2 ⟶ Y2},
      Nonempty (f₁ ≫ gY ≅ gX ≫ f₂) →
        ∀ [AlgebraicGeometry.AlgebraicStack.IsSchemeTheoreticImage f₁ toImage₁ ι₁]
          [AlgebraicGeometry.AlgebraicStack.IsSchemeTheoreticImage f₂ toImage₂ ι₂],
          ∃ h : Z1 ⟶ Z2, Nonempty (h ≫ ι₂ ≅ ι₁ ≫ gY) ∧
            Nonempty (gX ≫ toImage₂ ≅ toImage₁ ≫ h))
