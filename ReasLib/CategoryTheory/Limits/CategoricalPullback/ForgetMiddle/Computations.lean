/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.ForgetMiddle.Basic

/-!
# Computations for middle contraction

Projection and structural-isomorphism formulas for the middle-contraction transformation and its
explicit forward and inverse functors.
-/

@[expose] public section

open CategoryTheory.Limits
open CategoricalPullback
open scoped CategoricalPullback

namespace CategoryTheory

open Functor

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]
variable {C : Type u₃} [Category.{v₃} C]
variable {D : Type u₄} [Category.{v₄} D]

variable (F : A ⥤ B) (G : C ⥤ B) (H : D ⥤ C)

local notation "LeftAssoc" => (π₂ F G) ⊡ H
local notation "RightAssoc" => F ⊡ (H ⋙ G)

namespace Limits.CategoricalPullback.ForgetMiddle

namespace transform

/-- The left leg of the middle-contraction transform is the first projection. -/
@[simp]
theorem left :
    (ForgetMiddle.transform F G H).left = π₁ F G := sorry

/-- The base leg of the middle-contraction transform is `G`. -/
@[simp]
theorem base :
    (ForgetMiddle.transform F G H).base = G := sorry

/-- The right leg of the middle-contraction transform is the identity of `D`. -/
@[simp]
theorem right :
    (ForgetMiddle.transform F G H).right = 𝟭 D := sorry

/-- The left comparison cell of middle contraction is the inverse canonical pullback square. -/
@[simp]
theorem squareLeft.iso :
    (ForgetMiddle.transform F G H).squareLeft.iso = (catCommSq F G).iso.symm := sorry

/-- The right comparison cell of middle contraction is the inverse left unitor. -/
@[simp]
theorem squareRight.iso :
    (ForgetMiddle.transform F G H).squareRight.iso = (leftUnitor (H ⋙ G)).symm := sorry

end transform

namespace functor

/-- The forward component of the first-projection comparison for middle contraction is the
identity. -/
@[simp]
theorem fstIso.hom.app (X : LeftAssoc) :
    (ForgetMiddle.functor.fstIso F G H).hom.app X = 𝟙 _ := sorry

/-- The inverse component of the first-projection comparison for middle contraction is the
identity. -/
@[simp]
theorem fstIso.inv.app (X : LeftAssoc) :
    (ForgetMiddle.functor.fstIso F G H).inv.app X = 𝟙 _ := sorry

/-- The forward component of the second-projection comparison for middle contraction is the
right-unitor component of the source's second projection. -/
@[simp]
theorem sndIso.hom.app (X : LeftAssoc) :
    (ForgetMiddle.functor.sndIso F G H).hom.app X =
      (Functor.rightUnitor (π₂ (π₂ F G) H)).hom.app X := sorry

/-- The inverse component of the second-projection comparison for middle contraction is the
inverse right-unitor component of the source's second projection. -/
@[simp]
theorem sndIso.inv.app (X : LeftAssoc) :
    (ForgetMiddle.functor.sndIso F G H).inv.app X =
      (Functor.rightUnitor (π₂ (π₂ F G) H)).inv.app X := sorry

/-- Forgetting the middle object retains the leftmost object. -/
@[simp]
theorem obj.fst (X : LeftAssoc) :
    ((ForgetMiddle.functor F G H).obj X).fst = X.fst.fst := sorry

/-- Forgetting the middle object retains the rightmost object. -/
@[simp]
theorem obj.snd (X : LeftAssoc) :
    ((ForgetMiddle.functor F G H).obj X).snd = X.snd := sorry

/-- The structural isomorphism after middle contraction is the composite of the two source
isomorphisms, with the second mapped through `G`. -/
@[simp]
theorem obj.iso (X : LeftAssoc) :
    ((ForgetMiddle.functor F G H).obj X).iso = X.fst.iso ≪≫ G.mapIso X.iso := sorry

/-- The forward structural map after middle contraction is the composite of the inner comparison
and the `G`-image of the outer comparison. -/
@[simp]
theorem obj.iso.hom (X : LeftAssoc) :
    ((ForgetMiddle.functor F G H).obj X).iso.hom =
      X.fst.iso.hom ≫ G.map X.iso.hom := sorry

/-- The inverse structural map after middle contraction reverses the `G`-image of the outer
comparison and the inner comparison. -/
@[simp]
theorem obj.iso.inv (X : LeftAssoc) :
    ((ForgetMiddle.functor F G H).obj X).iso.inv =
      G.map X.iso.inv ≫ X.fst.iso.inv := sorry

/-- On morphisms, forgetting the middle object retains the leftmost component. -/
@[simp]
theorem hom.fst {X Y : LeftAssoc} (f : X ⟶ Y) :
    ((ForgetMiddle.functor F G H).map f).fst = f.fst.fst := sorry

/-- On morphisms, forgetting the middle object retains the rightmost component. -/
@[simp]
theorem hom.snd {X Y : LeftAssoc} (f : X ⟶ Y) :
    ((ForgetMiddle.functor F G H).map f).snd = f.snd := sorry

end functor

namespace inverse

/-- Inserting the middle object retains the leftmost object. -/
@[simp]
theorem obj.fstFst (X : RightAssoc) :
    ((ForgetMiddle.inverse F G H).obj X).fst.fst = X.fst := sorry

/-- Inserting the middle object chooses `H.obj X.snd` as its new middle object. -/
@[simp]
theorem obj.fstSnd (X : RightAssoc) :
    ((ForgetMiddle.inverse F G H).obj X).fst.snd = H.obj X.snd := sorry

/-- The inner structural isomorphism of an inserted object is the original one. -/
@[simp]
theorem obj.fstIso (X : RightAssoc) :
    ((ForgetMiddle.inverse F G H).obj X).fst.iso = X.iso := sorry

/-- Inserting the middle object retains the rightmost object. -/
@[simp]
theorem obj.snd (X : RightAssoc) :
    ((ForgetMiddle.inverse F G H).obj X).snd = X.snd := sorry

/-- The outer structural isomorphism of an inserted object is the identity. -/
@[simp]
theorem obj.iso (X : RightAssoc) :
    ((ForgetMiddle.inverse F G H).obj X).iso = Iso.refl (H.obj X.snd) := sorry

/-- On morphisms, insertion retains the leftmost component. -/
@[simp]
theorem hom.fstFst {X Y : RightAssoc} (f : X ⟶ Y) :
    ((ForgetMiddle.inverse F G H).map f).fst.fst = f.fst := sorry

/-- On morphisms, insertion applies `H` to the new middle component. -/
@[simp]
theorem hom.fstSnd {X Y : RightAssoc} (f : X ⟶ Y) :
    ((ForgetMiddle.inverse F G H).map f).fst.snd = H.map f.snd := sorry

/-- On morphisms, insertion retains the rightmost component. -/
@[simp]
theorem hom.snd {X Y : RightAssoc} (f : X ⟶ Y) :
    ((ForgetMiddle.inverse F G H).map f).snd = f.snd := sorry

end inverse

end Limits.CategoricalPullback.ForgetMiddle

end CategoryTheory
