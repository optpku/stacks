/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Functor.AsSmall
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Bilimit

/-!
# Universe resizing for categorical pullback squares

The bicategory `Cat` is universe-homogeneous: all category objects in one cospan must use the same
object and Hom universes. A general `CatCommSqOver` has no such restriction. This file gives the
canonical bridge by transporting all four categories to common `AsSmall` models.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe vA uA vB uB vC uC vX uX

namespace CategoryTheory.Limits.CategoricalPullback.CatCommSqOver

variable {A : Type uA} [Category.{vA} A]
variable {B : Type uB} [Category.{vB} B]
variable {C : Type uC} [Category.{vC} C]
variable {X : Type uX} [Category.{vX} X]
variable {F : A ⥤ C} {G : B ⥤ C}

/-- A categorical commutative square transported to common small models of its four categories. -/
def resize (P : CatCommSqOver F G X) :
    CatCommSqOver
      (Functor.asSmall.{max vB uB vX uX} F)
      (Functor.asSmall.{max vA uA vX uX} G)
      (AsSmall.{max vA uA vB uB vC uC vX uX} X) where
  fst := Functor.asSmall.{max vB uB vC uC} P.fst
  snd := Functor.asSmall.{max vA uA vC uC} P.snd
  iso := Functor.asSmallMapIso.{max vA uA vB uB} P.iso

namespace Resized

/-- The universe-independent bilimit predicate for a categorical commutative square: resize the
square canonically and apply the ordinary `Cat`-bilimit predicate. -/
abbrev IsBilimit (P : CatCommSqOver F G X) : Prop :=
  P.resize.IsBilimit

end Resized

end CategoryTheory.Limits.CategoricalPullback.CatCommSqOver
