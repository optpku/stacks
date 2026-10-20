/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Cone
public import ReasLib.CategoryTheory.Bicategory.Square

@[expose] public section

open scoped CategoryTheory.Bicategory

universe w v u

namespace CategoryTheory

open Bicategory

namespace Bicategory.PseudoPullbackCone

variable {B : Type u} [Bicategory.{w, v} B]
variable {T X' Y' X Y : B} {y : T ⟶ Y'} {p : X' ⟶ Y'}
variable (S : Bicategory.PseudoPullbackCone y p)
variable {q : X' ⟶ X} {g : Y' ⟶ Y} {f : X ⟶ Y}

/-- Postcomposing a `2`-commutative square with a right square gives the outer rectangle. -/
def postcompose (φ : p ≫ g ≅ q ≫ f) :
    Bicategory.PseudoPullbackCone (y ≫ g) f where
  pt := S.pt
  fst := S.fst
  snd := S.snd ≫ q
  iso := pasteSquareIso S.iso φ

/-- Postcomposition retains the apex of the original pseudopullback cone. -/
@[simp] theorem postcompose.pt (φ : p ≫ g ≅ q ≫ f) :
    (S.postcompose φ).pt = S.pt := sorry

/-- Postcomposition retains the left leg of the original pseudopullback cone. -/
@[simp] theorem postcompose.fst (φ : p ≫ g ≅ q ≫ f) :
    (S.postcompose φ).fst = S.fst := sorry

/-- The right leg of a postcomposed cone is the original right leg followed by the right-square
leg. -/
@[simp] theorem postcompose.snd (φ : p ≫ g ≅ q ≫ f) :
    (S.postcompose φ).snd = S.snd ≫ q := sorry

/-- The comparison of a postcomposed cone is the canonical pasting of the original comparison
with the right-square comparison. -/
@[simp] theorem postcompose.iso (φ : p ≫ g ≅ q ≫ f) :
    (S.postcompose φ).iso = pasteSquareIso S.iso φ := sorry

/-- The forward comparison cell of a postcomposed cone is the forward pasting of the original
comparison and the right-square comparison. -/
@[simp] theorem postcompose.iso.hom (φ : p ≫ g ≅ q ≫ f) :
    (S.postcompose φ).iso.hom =
      (α_ S.fst y g).inv ≫ (whiskerRightIso S.iso g).hom ≫
        (α_ S.snd p g).hom ≫ (whiskerLeftIso S.snd φ).hom ≫
          (α_ S.snd q f).inv := sorry

/-- The inverse comparison cell of a postcomposed cone is the reverse pasting of the inverse
right-square and original comparisons. -/
@[simp] theorem postcompose.iso.inv (φ : p ≫ g ≅ q ≫ f) :
    (S.postcompose φ).iso.inv =
      (α_ S.snd q f).hom ≫ (whiskerLeftIso S.snd φ).inv ≫
        (α_ S.snd p g).inv ≫ (whiskerRightIso S.iso g).inv ≫
          (α_ S.fst y g).hom := sorry

/-- Iterated postcomposition has the same comparison as postcomposition by the
pasted right-hand square, after the canonical reassociation of the two outer
boundary paths.

The associators are part of the statement: the iterated and single
postcompositions use different parenthesizations and therefore are not
definitionally equal cones. -/
theorem postcompose.iso.assoc
    {W Z : B} {r : X ⟶ W} {h : Y ⟶ Z} {k : W ⟶ Z}
    (φ : p ≫ g ≅ q ≫ f) (ψ : f ≫ h ≅ r ≫ k) :
    ((S.postcompose φ).postcompose ψ).iso ≪≫
        whiskerRightIso (α_ S.snd q r) k =
      whiskerLeftIso S.fst (α_ y g h) ≪≫
        (S.postcompose (pasteSquareIso φ ψ)).iso := sorry

end Bicategory.PseudoPullbackCone

end CategoryTheory
