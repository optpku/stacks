/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.CommSq
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeTheoreticImage
public import stacks_project.Chap67.Definition_67_13_2_InverseImage

/-!
# Scheme-theoretic images of morphisms of algebraic spaces

A closed immersion `ι : Z ⟶ Y` is a scheme-theoretic image of `f : X ⟶ Y` via
`toImage : X ⟶ Z` when `f` factors through `ι` and `ι` is least among closed
immersions with that property. Functoriality of this factorization along a
commutative square is stated at the existence/universal-property layer: there is
no chosen `Hom.image` carrier.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.AlgebraicSpace

#check (IsSchemeTheoreticImage :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S},
    (X ⟶ Y) → (X ⟶ Z) → (Z ⟶ Y) → Prop)

#check (IsSchemeTheoreticImage.spec :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (toImage : X ⟶ Z) (ι : Z ⟶ Y),
    IsSchemeTheoreticImage f toImage ι ↔
      toImage ≫ ι = f ∧ IsClosedImmersion ι ∧
        ∀ {Z' : AlgebraicSpace S} (toZ' : X ⟶ Z') (ι' : Z' ⟶ Y)
          [IsClosedImmersion ι'], toZ' ≫ ι' = f →
          ∃! lift : Z ⟶ Z', lift ≫ ι' = ι ∧ toImage ≫ lift = toZ')

#check (IsSchemeTheoreticImage.lift :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    {f : X ⟶ Y} {toImage : X ⟶ Z} {ι : Z ⟶ Y}
    [IsSchemeTheoreticImage f toImage ι] {Z' : AlgebraicSpace S}
    (toZ' : X ⟶ Z') (ι' : Z' ⟶ Y) [IsClosedImmersion ι']
    (hfac : toZ' ≫ ι' = f),
    ∃! lift : Z ⟶ Z', lift ≫ ι' = ι ∧ toImage ≫ lift = toZ')

#check (IsSchemeTheoreticImage.of_isClosedImmersion :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsClosedImmersion f], IsSchemeTheoreticImage f (𝟙 X) f)

#check (IsSchemeTheoreticImage.id :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S},
    IsSchemeTheoreticImage (𝟙 X) (𝟙 X) (𝟙 X))

#check (IsSchemeTheoreticImage.of_isIso :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsIso f], IsSchemeTheoreticImage f f (𝟙 Y))

#check (IsSchemeTheoreticImage.exists_imageMap :
  ∀ {S : Scheme.{u}}
    {X1 X2 Y1 Y2 Z1 Z2 : AlgebraicSpace S}
    {f₁ : X1 ⟶ Y1} {f₂ : X2 ⟶ Y2} {gX : X1 ⟶ X2} {gY : Y1 ⟶ Y2}
    {toImage₁ : X1 ⟶ Z1} {ι₁ : Z1 ⟶ Y1} {toImage₂ : X2 ⟶ Z2} {ι₂ : Z2 ⟶ Y2}
    (sq : CommSq gX f₁ f₂ gY)
    [IsSchemeTheoreticImage f₁ toImage₁ ι₁]
    [IsSchemeTheoreticImage f₂ toImage₂ ι₂],
    ∃ h : Z1 ⟶ Z2, CommSq h ι₁ ι₂ gY ∧ CommSq gX toImage₁ toImage₂ h)

#check (IsSchemeTheoreticImage.existsUnique_imageMap :
  ∀ {S : Scheme.{u}}
    {X1 X2 Y1 Y2 Z1 Z2 : AlgebraicSpace S}
    {f₁ : X1 ⟶ Y1} {f₂ : X2 ⟶ Y2} {gX : X1 ⟶ X2} {gY : Y1 ⟶ Y2}
    {toImage₁ : X1 ⟶ Z1} {ι₁ : Z1 ⟶ Y1} {toImage₂ : X2 ⟶ Z2} {ι₂ : Z2 ⟶ Y2}
    (sq : CommSq gX f₁ f₂ gY)
    [IsSchemeTheoreticImage f₁ toImage₁ ι₁]
    [IsSchemeTheoreticImage f₂ toImage₂ ι₂],
    ∃! h : Z1 ⟶ Z2, CommSq h ι₁ ι₂ gY ∧ CommSq gX toImage₁ toImage₂ h)

#check (IsSchemeTheoreticImage.le_inverseImage :
  ∀ {S : Scheme.{u}}
    {X1 X2 Y1 Y2 Z1 Z2 : AlgebraicSpace S}
    {f₁ : X1 ⟶ Y1} {f₂ : X2 ⟶ Y2} {gX : X1 ⟶ X2} {gY : Y1 ⟶ Y2}
    {toImage₁ : X1 ⟶ Z1} {ι₁ : Z1 ⟶ Y1} {toImage₂ : X2 ⟶ Z2} {ι₂ : Z2 ⟶ Y2}
    (sq : CommSq gX f₁ f₂ gY)
    [IsSchemeTheoreticImage f₁ toImage₁ ι₁]
    [IsSchemeTheoreticImage f₂ toImage₂ ι₂]
    [IsClosedImmersion ι₂],
    ∃ k : Z1 ⟶ inverseImage gY ι₂, k ≫ inverseImageι gY ι₂ = ι₁)

end AlgebraicGeometry.AlgebraicSpace
