module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeTheoreticImage
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 67.16.6: Let `S` be a scheme. A commutative square of algebraic spaces
over `S` induces a morphism between the scheme-theoretic images of the
horizontal maps, filling the two squares `X₁ ⟶ Z₁ ⟶ Y₁` over `X₂ ⟶ Z₂ ⟶ Y₂`. -/
@[stacks 0CP2] #check
  (AlgebraicGeometry.AlgebraicSpace.IsSchemeTheoreticImage.exists_imageMap :
    ∀ {S : Scheme.{u}} {X1 X2 Y1 Y2 Z1 Z2 : AlgebraicSpace S}
      {f₁ : X1 ⟶ Y1} {f₂ : X2 ⟶ Y2} {gX : X1 ⟶ X2} {gY : Y1 ⟶ Y2}
      {toImage₁ : X1 ⟶ Z1} {ι₁ : Z1 ⟶ Y1}
      {toImage₂ : X2 ⟶ Z2} {ι₂ : Z2 ⟶ Y2},
      CommSq gX f₁ f₂ gY →
        ∀ [AlgebraicGeometry.AlgebraicSpace.IsSchemeTheoreticImage f₁ toImage₁ ι₁]
          [AlgebraicGeometry.AlgebraicSpace.IsSchemeTheoreticImage f₂ toImage₂ ι₂],
          ∃ h : Z1 ⟶ Z2, CommSq h ι₁ ι₂ gY ∧ CommSq gX toImage₁ toImage₂ h)
