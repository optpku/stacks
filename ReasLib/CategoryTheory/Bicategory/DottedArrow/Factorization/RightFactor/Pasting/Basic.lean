/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.DottedArrow.Factorization.RightFactor.Basic

@[expose] public section

open scoped CategoryTheory.Bicategory

universe w v u

namespace CategoryTheory

open Bicategory

namespace DottedArrow

variable {B : Type u} [Bicategory.{w, v} B]
variable {T X Y Z : B} {z : T ⟶ Z} {f : X ⟶ Y} {g : Y ⟶ Z}
variable (sq : Bicategory.PseudoPullbackCone z (f ≫ g))

section PasteFunctorImplementation

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace Implementation

/-- The lower-right comparison obtained by pasting a left-factor dotted arrow with d. -/
private def pasteRightIso
    (d : DottedArrow (Bicategory.PseudoPullbackCone.factorRight sq))
    (A : DottedArrow (leftFactorSquare sq d)) :
    z ≅ A.arrow ≫ (f ≫ g) :=
  d.right ≪≫ whiskerRightIso A.right g ≪≫ α_ A.arrow f g

/-- The pasted comparisons satisfy the original outer-square coherence.

Proof strategy: whisker A.comm by g, substitute d.comm, and normalize associators and whiskering
exchange identities. -/
private theorem pasteObj_comm
    (d : DottedArrow (Bicategory.PseudoPullbackCone.factorRight sq))
    (A : DottedArrow (leftFactorSquare sq d)) :
    whiskerLeftIso sq.fst (pasteRightIso sq d A) ≪≫
        (α_ sq.fst A.arrow (f ≫ g)).symm ≪≫
          whiskerRightIso A.left (f ≫ g) =
      sq.iso := sorry

/-- Paste a dotted arrow for the left factor with the fixed middle dotted arrow. -/
private def pasteObj
    (d : DottedArrow (Bicategory.PseudoPullbackCone.factorRight sq))
    (A : DottedArrow (leftFactorSquare sq d)) :
    DottedArrow sq where
  arrow := A.arrow
  left := A.left
  right := pasteRightIso sq d A
  comm := pasteObj_comm sq d A

/-- Left-comparison compatibility for a pasted morphism.

Proof strategy: use η.left_comm directly. -/
private theorem pasteMap_left_comm
    (d : DottedArrow (Bicategory.PseudoPullbackCone.factorRight sq))
    {A A' : DottedArrow (leftFactorSquare sq d)} (η : A ⟶ A') :
    sq.fst ◁ η.hom ≫ (pasteObj sq d A').left.hom =
      (pasteObj sq d A).left.hom := sorry

/-- Right-comparison compatibility for a pasted morphism.

Proof strategy: whisker η.right_comm by g and use associator naturality. -/
private theorem pasteMap_right_comm
    (d : DottedArrow (Bicategory.PseudoPullbackCone.factorRight sq))
    {A A' : DottedArrow (leftFactorSquare sq d)} (η : A ⟶ A') :
    (pasteObj sq d A).right.hom ≫ η.hom ▷ (f ≫ g) =
      (pasteObj sq d A').right.hom := sorry

/-- The outer dotted-arrow morphism obtained by pasting a left-factor morphism. -/
private def pasteMap
    (d : DottedArrow (Bicategory.PseudoPullbackCone.factorRight sq))
    {A A' : DottedArrow (leftFactorSquare sq d)} (η : A ⟶ A') :
    pasteObj sq d A ⟶ pasteObj sq d A' where
  hom := η.hom
  left_comm := pasteMap_left_comm sq d η
  right_comm := pasteMap_right_comm sq d η

/-- Pasting preserves identity dotted-arrow morphisms.

Proof strategy: apply DottedArrow.Hom.ext; the ambient component is the identity. -/
private theorem pasteMap_id
    (d : DottedArrow (Bicategory.PseudoPullbackCone.factorRight sq))
    (A : DottedArrow (leftFactorSquare sq d)) :
    pasteMap sq d (𝟙 A) = 𝟙 (pasteObj sq d A) := sorry

/-- Pasting preserves composition of dotted-arrow morphisms.

Proof strategy: apply DottedArrow.Hom.ext; the ambient component is the original composite. -/
private theorem pasteMap_comp
    (d : DottedArrow (Bicategory.PseudoPullbackCone.factorRight sq))
    {A A' A'' : DottedArrow (leftFactorSquare sq d)}
    (η : A ⟶ A') (θ : A' ⟶ A'') :
    pasteMap sq d (η ≫ θ) = pasteMap sq d η ≫ pasteMap sq d θ := sorry

end Implementation

/-- The functor that pastes left-factor dotted arrows back into outer dotted arrows. -/
def pasteFunctor
    (d : DottedArrow (Bicategory.PseudoPullbackCone.factorRight sq)) :
    DottedArrow (leftFactorSquare sq d) ⥤ DottedArrow sq where
  obj := Implementation.pasteObj sq d
  map := Implementation.pasteMap sq d
  map_id := Implementation.pasteMap_id sq d
  map_comp := Implementation.pasteMap_comp sq d

end PasteFunctorImplementation

/-- The arrow underlying the paste of a left-factor dotted arrow.

Proof strategy: unfold pasteFunctor and its private object implementation. -/
@[simp] theorem pasteFunctor.obj.arrow
    (d : DottedArrow (Bicategory.PseudoPullbackCone.factorRight sq))
    (A : DottedArrow (leftFactorSquare sq d)) :
    ((pasteFunctor sq d).obj A).arrow = A.arrow := sorry

/-- The left comparison of the paste of a left-factor dotted arrow.

Proof strategy: unfold pasteFunctor and its private object implementation. -/
@[simp] theorem pasteFunctor.obj.left
    (d : DottedArrow (Bicategory.PseudoPullbackCone.factorRight sq))
    (A : DottedArrow (leftFactorSquare sq d)) :
    ((pasteFunctor sq d).obj A).left = A.left := sorry

/-- The right comparison of the paste of a left-factor dotted arrow.

Proof strategy: unfold pasteFunctor and its private object implementation. -/
@[simp] theorem pasteFunctor.obj.right
    (d : DottedArrow (Bicategory.PseudoPullbackCone.factorRight sq))
    (A : DottedArrow (leftFactorSquare sq d)) :
    ((pasteFunctor sq d).obj A).right =
      d.right ≪≫ whiskerRightIso A.right g ≪≫ α_ A.arrow f g := sorry

/-- The ambient 2-morphism underlying the paste of a left-factor morphism.

Proof strategy: unfold pasteFunctor and its private map implementation. -/
@[simp] theorem pasteFunctor.map.hom
    (d : DottedArrow (Bicategory.PseudoPullbackCone.factorRight sq))
    {A A' : DottedArrow (leftFactorSquare sq d)} (η : A ⟶ A') :
    ((pasteFunctor sq d).map η).hom = η.hom := sorry

/-- The mapped ambient cell satisfies the left triangular compatibility after
pasting. -/
@[simp]
theorem pasteFunctor.map.leftComm
    (d : DottedArrow (Bicategory.PseudoPullbackCone.factorRight sq))
    {A A' : DottedArrow (leftFactorSquare sq d)} (η : A ⟶ A') :
    sq.fst ◁ ((pasteFunctor sq d).map η).hom ≫
        ((pasteFunctor sq d).obj A').left.hom =
      ((pasteFunctor sq d).obj A).left.hom := sorry

/-- The mapped ambient cell satisfies the right triangular compatibility after
pasting. -/
@[simp]
theorem pasteFunctor.map.rightComm
    (d : DottedArrow (Bicategory.PseudoPullbackCone.factorRight sq))
    {A A' : DottedArrow (leftFactorSquare sq d)} (η : A ⟶ A') :
    ((pasteFunctor sq d).obj A).right.hom ≫
        ((pasteFunctor sq d).map η).hom ▷ (f ≫ g) =
      ((pasteFunctor sq d).obj A').right.hom := sorry

end DottedArrow

end CategoryTheory
