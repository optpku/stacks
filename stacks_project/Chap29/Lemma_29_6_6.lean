/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.SchemeTheoreticImage.Functorial
import StacksCheckRecall

/-!
# Lemma 29.6.6

Functoriality of scheme-theoretic images under commutative squares.

@stack 01R9
-/

@[expose] public section

/- Lemma 29.6.6: A commutative square of scheme morphisms induces a morphism between
their scheme-theoretic images. -/
@[stacks 01R9] #check
  (@AlgebraicGeometry.Scheme.Hom.imageMap :
    ∀ {X1 X2 Y1 Y2 : AlgebraicGeometry.Scheme}
      {f₁ : X1 ⟶ Y1} {f₂ : X2 ⟶ Y2}
      {gX : X1 ⟶ X2} {gY : Y1 ⟶ Y2},
      CategoryTheory.CommSq gX f₁ f₂ gY →
        AlgebraicGeometry.Scheme.Hom
          (AlgebraicGeometry.Scheme.Hom.image f₁)
          (AlgebraicGeometry.Scheme.Hom.image f₂))

#check
  (@AlgebraicGeometry.Scheme.Hom.imageMap_commSq :
    ∀ {X1 X2 Y1 Y2 : AlgebraicGeometry.Scheme}
      {f₁ : X1 ⟶ Y1} {f₂ : X2 ⟶ Y2}
      {gX : X1 ⟶ X2} {gY : Y1 ⟶ Y2}
      (sq : CategoryTheory.CommSq gX f₁ f₂ gY),
      CategoryTheory.CommSq
        (AlgebraicGeometry.Scheme.Hom.imageMap sq)
        (AlgebraicGeometry.Scheme.Hom.imageι f₁)
        (AlgebraicGeometry.Scheme.Hom.imageι f₂) gY)

#check
  (@AlgebraicGeometry.Scheme.Hom.toImage_imageMap_commSq :
    ∀ {X1 X2 Y1 Y2 : AlgebraicGeometry.Scheme}
      {f₁ : X1 ⟶ Y1} {f₂ : X2 ⟶ Y2}
      {gX : X1 ⟶ X2} {gY : Y1 ⟶ Y2}
      (sq : CategoryTheory.CommSq gX f₁ f₂ gY),
      CategoryTheory.CommSq gX
        (AlgebraicGeometry.Scheme.Hom.toImage f₁)
        (AlgebraicGeometry.Scheme.Hom.toImage f₂)
        (AlgebraicGeometry.Scheme.Hom.imageMap sq))
