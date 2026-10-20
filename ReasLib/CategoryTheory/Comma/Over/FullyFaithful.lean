/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Costructured arrows along fully faithful functors

A fully faithful functor identifies costructured arrows ending at an object in its image with
the corresponding slice category in its source.  This owner is independent of presheaves and
categories of elements.
-/

@[expose] public section

universe vD uD vC uC

namespace CategoryTheory.CostructuredArrow

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]

/-- A fully faithful functor identifies costructured arrows ending at `F.obj X` with the slice
category over `X` in its source. -/
@[stacks 0044 "fully faithful costructured-arrow equivalence"]
noncomputable def overEquivalence.ofFullyFaithful
    (F : C ⥤ D) [F.Full] [F.Faithful] (X : C) :
    CostructuredArrow F (F.obj X) ≌ Over X :=
  (CostructuredArrow.post (𝟭 C) F X).asEquivalence.symm

namespace overEquivalence.ofFullyFaithful

variable (F : C ⥤ D) [F.Full] [F.Faithful]

/-- The inverse of the fully-faithful costructured-arrow equivalence retains the source object
of a slice arrow. -/
@[simp]
theorem inverse.obj.left (X : C) (a : Over X) :
    ((overEquivalence.ofFullyFaithful F X).inverse.obj a).left = a.left := sorry

/-- The inverse of the fully-faithful costructured-arrow equivalence applies `F` to the
structure arrow of a slice object. -/
@[simp]
theorem inverse.obj.hom (X : C) (a : Over X) :
    ((overEquivalence.ofFullyFaithful F X).inverse.obj a).hom =
      F.map a.hom := sorry

/-- The inverse of the fully-faithful costructured-arrow equivalence retains the underlying
arrow of a slice morphism. -/
@[simp]
theorem inverse.map.left (X : C) {a b : Over X} (f : a ⟶ b) :
    ((overEquivalence.ofFullyFaithful F X).inverse.map f).left = f.left := sorry

/-- The inverse of the fully-faithful costructured-arrow equivalence strictly preserves the
projection to the source category. -/
theorem inverse.comm (X : C) :
    (overEquivalence.ofFullyFaithful F X).inverse ⋙
        CostructuredArrow.proj F (F.obj X) =
      Over.forget X := sorry

/-- The canonical comparison from the source of a costructured arrow to the source selected by
the fully-faithful inverse equivalence. -/
noncomputable def functor.obj.leftIso (X : C)
    (a : CostructuredArrow F (F.obj X)) :
    a.left ≅ ((overEquivalence.ofFullyFaithful F X).functor.obj a).left :=
  Comma.leftIso ((overEquivalence.ofFullyFaithful F X).unitIso.app a)

/-- The forward source comparison identifies the original structure arrow with the image under
`F` of the selected slice arrow. -/
@[reassoc]
theorem functor.obj.leftIso.hom.w (X : C)
    (a : CostructuredArrow F (F.obj X)) :
    F.map (functor.obj.leftIso F X a).hom ≫
        F.map ((overEquivalence.ofFullyFaithful F X).functor.obj a).hom =
      a.hom := sorry

/-- The inverse source comparison identifies the image of the selected slice arrow with the
original structure arrow. -/
@[reassoc]
theorem functor.obj.leftIso.inv.w (X : C)
    (a : CostructuredArrow F (F.obj X)) :
    F.map (functor.obj.leftIso F X a).inv ≫ a.hom =
      F.map ((overEquivalence.ofFullyFaithful F X).functor.obj a).hom := sorry

/-- The forward source comparisons are natural in costructured-arrow morphisms. -/
@[reassoc]
theorem functor.map.leftIso.hom (X : C)
    {a b : CostructuredArrow F (F.obj X)} (f : a ⟶ b) :
    f.left ≫ (functor.obj.leftIso F X b).hom =
      (functor.obj.leftIso F X a).hom ≫
        ((overEquivalence.ofFullyFaithful F X).functor.map f).left := sorry

/-- The inverse source comparisons are natural in costructured-arrow morphisms. -/
@[reassoc]
theorem functor.map.leftIso.inv (X : C)
    {a b : CostructuredArrow F (F.obj X)} (f : a ⟶ b) :
    ((overEquivalence.ofFullyFaithful F X).functor.map f).left ≫
        (functor.obj.leftIso F X b).inv =
      (functor.obj.leftIso F X a).inv ≫ f.left := sorry

/-- The forward fully-faithful costructured-arrow equivalence preserves the projection to the
source category up to the canonical source comparison. -/
noncomputable def functor.projIso (X : C) :
    CostructuredArrow.proj F (F.obj X) ≅
      (overEquivalence.ofFullyFaithful F X).functor ⋙ Over.forget X :=
  NatIso.ofComponents (functor.obj.leftIso F X)
    (functor.map.leftIso.hom F X)

/-- The forward component of the projection comparison is the canonical source comparison. -/
@[simp]
theorem functor.projIso.hom.app (X : C)
    (a : CostructuredArrow F (F.obj X)) :
    (functor.projIso F X).hom.app a =
      (functor.obj.leftIso F X a).hom := sorry

/-- The inverse component of the projection comparison is the inverse canonical source
comparison. -/
@[simp]
theorem functor.projIso.inv.app (X : C)
    (a : CostructuredArrow F (F.obj X)) :
    (functor.projIso F X).inv.app a =
      (functor.obj.leftIso F X a).inv := sorry

/-- The source comparison for target postcomposition satisfies the slice-triangle equation. -/
theorem mapIsoApp.w {X Y : C} (f : X ⟶ Y)
    (a : CostructuredArrow F (F.obj X)) :
    ((functor.obj.leftIso F X a).symm ≪≫
          functor.obj.leftIso F Y ((CostructuredArrow.map (F.map f)).obj a)).hom ≫
        ((overEquivalence.ofFullyFaithful F Y).functor.obj
          ((CostructuredArrow.map (F.map f)).obj a)).hom =
      ((overEquivalence.ofFullyFaithful F X).functor.obj a).hom ≫ f := sorry

/-- Objectwise comparison between postcomposition in slices and postcomposition of
costructured arrows under a fully faithful functor. -/
noncomputable def mapIsoApp {X Y : C} (f : X ⟶ Y)
    (a : CostructuredArrow F (F.obj X)) :
    ((overEquivalence.ofFullyFaithful F X).functor ⋙ Over.map f).obj a ≅
      (CostructuredArrow.map (F.map f) ⋙
        (overEquivalence.ofFullyFaithful F Y).functor).obj a :=
  Over.isoMk
    ((functor.obj.leftIso F X a).symm ≪≫
      functor.obj.leftIso F Y ((CostructuredArrow.map (F.map f)).obj a))
    (mapIsoApp.w F f a)

/-- The objectwise target-postcomposition comparisons are natural in costructured arrows. -/
theorem mapIsoApp.naturality {X Y : C} (f : X ⟶ Y)
    {a b : CostructuredArrow F (F.obj X)} (g : a ⟶ b) :
    ((overEquivalence.ofFullyFaithful F X).functor ⋙ Over.map f).map g ≫
        (mapIsoApp F f b).hom =
      (mapIsoApp F f a).hom ≫
        (CostructuredArrow.map (F.map f) ⋙
          (overEquivalence.ofFullyFaithful F Y).functor).map g := sorry

/-- The fully-faithful costructured-arrow equivalence is natural under postcomposition of the
target object. -/
noncomputable def mapIso {X Y : C} (f : X ⟶ Y) :
    (overEquivalence.ofFullyFaithful F X).functor ⋙ Over.map f ≅
      CostructuredArrow.map (F.map f) ⋙
        (overEquivalence.ofFullyFaithful F Y).functor :=
  NatIso.ofComponents (mapIsoApp F f) (mapIsoApp.naturality F f)

/-- The underlying forward arrow of target naturality is the composite of the two canonical
source comparisons. -/
@[simp]
theorem mapIso.hom.app.left {X Y : C} (f : X ⟶ Y)
    (a : CostructuredArrow F (F.obj X)) :
    ((mapIso F f).hom.app a).left =
      ((functor.obj.leftIso F X a).symm ≪≫
        functor.obj.leftIso F Y ((CostructuredArrow.map (F.map f)).obj a)).hom := sorry

/-- The underlying inverse arrow of target naturality is the inverse composite of the two
canonical source comparisons. -/
@[simp]
theorem mapIso.inv.app.left {X Y : C} (f : X ⟶ Y)
    (a : CostructuredArrow F (F.obj X)) :
    ((mapIso F f).inv.app a).left =
      ((functor.obj.leftIso F X a).symm ≪≫
        functor.obj.leftIso F Y ((CostructuredArrow.map (F.map f)).obj a)).inv := sorry

end overEquivalence.ofFullyFaithful

end CategoryTheory.CostructuredArrow
