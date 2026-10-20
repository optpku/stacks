/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Bounded.Composition
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Bounded.Naturality
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Composition.Naturality
import Mathlib.Tactic.CrossRefAttribute

/-!
# Naturality of bounded exact-derived composition comparisons

The composition comparisons on bounded-below, bounded-above, and bounded
derived categories are natural in both exact functors.  The one-variable
specializations avoid horizontal-composition boilerplate in downstream
calculations.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe w₁ w₂ w₃ v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.ExactFunctor.Derived

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]
variable {C : Type u₃} [Category.{v₃} C] [Abelian C] [HasDerivedCategory.{w₃} C]

namespace Plus

/-- The bounded-below composition comparison is natural in both exact
functors. -/
@[reassoc, stacks 015F "naturality of bounded-below exact-derived composition"]
theorem compFunctorIso.naturality
    {F F' : A ⥤ₑ B} (α : F ⟶ F') {G G' : B ⥤ₑ C} (β : G ⟶ G') :
    map (ExactFunctor.hcomp α β) ≫ (compFunctorIso F' G').hom =
      (compFunctorIso F G).hom ≫
        NatTrans.hcomp (map α) (map β) := sorry

/-- The inverse bounded-below composition comparison is natural in both
exact functors. -/
@[reassoc]
theorem compFunctorIso.inv_naturality
    {F F' : A ⥤ₑ B} (α : F ⟶ F') {G G' : B ⥤ₑ C} (β : G ⟶ G') :
    NatTrans.hcomp (map α) (map β) ≫
        (compFunctorIso F' G').inv =
      (compFunctorIso F G).inv ≫
        map (ExactFunctor.hcomp α β) := sorry

/-- The bounded-below composition comparison is natural in its first exact
functor. -/
@[reassoc]
theorem compFunctorIso.naturality_left
    {F F' : A ⥤ₑ B} (α : F ⟶ F') (G : B ⥤ₑ C) :
    map (ExactFunctor.whiskerRight α G) ≫
        (compFunctorIso F' G).hom =
      (compFunctorIso F G).hom ≫
        Functor.whiskerRight (map α) (functor G) := sorry

/-- The bounded-below composition comparison is natural in its second exact
functor. -/
@[reassoc]
theorem compFunctorIso.naturality_right
    (F : A ⥤ₑ B) {G G' : B ⥤ₑ C} (β : G ⟶ G') :
    map (ExactFunctor.whiskerLeft F β) ≫
        (compFunctorIso F G').hom =
      (compFunctorIso F G).hom ≫
        Functor.whiskerLeft (functor F) (map β) := sorry

/-- The inverse bounded-below composition comparison is natural in its
first exact functor. -/
@[reassoc]
theorem compFunctorIso.inv_naturality_left
    {F F' : A ⥤ₑ B} (α : F ⟶ F') (G : B ⥤ₑ C) :
    Functor.whiskerRight (map α) (functor G) ≫
        (compFunctorIso F' G).inv =
      (compFunctorIso F G).inv ≫
        map (ExactFunctor.whiskerRight α G) := sorry

/-- The inverse bounded-below composition comparison is natural in its
second exact functor. -/
@[reassoc]
theorem compFunctorIso.inv_naturality_right
    (F : A ⥤ₑ B) {G G' : B ⥤ₑ C} (β : G ⟶ G') :
    Functor.whiskerLeft (functor F) (map β) ≫
        (compFunctorIso F G').inv =
      (compFunctorIso F G).inv ≫
        map (ExactFunctor.whiskerLeft F β) := sorry

end Plus

namespace Minus

/-- The bounded-above composition comparison is natural in both exact
functors. -/
@[reassoc, stacks 015F "naturality of bounded-above exact-derived composition"]
theorem compFunctorIso.naturality
    {F F' : A ⥤ₑ B} (α : F ⟶ F') {G G' : B ⥤ₑ C} (β : G ⟶ G') :
    map (ExactFunctor.hcomp α β) ≫ (compFunctorIso F' G').hom =
      (compFunctorIso F G).hom ≫
        NatTrans.hcomp (map α) (map β) := sorry

/-- The inverse bounded-above composition comparison is natural in both
exact functors. -/
@[reassoc]
theorem compFunctorIso.inv_naturality
    {F F' : A ⥤ₑ B} (α : F ⟶ F') {G G' : B ⥤ₑ C} (β : G ⟶ G') :
    NatTrans.hcomp (map α) (map β) ≫
        (compFunctorIso F' G').inv =
      (compFunctorIso F G).inv ≫
        map (ExactFunctor.hcomp α β) := sorry

/-- The bounded-above composition comparison is natural in its first exact
functor. -/
@[reassoc]
theorem compFunctorIso.naturality_left
    {F F' : A ⥤ₑ B} (α : F ⟶ F') (G : B ⥤ₑ C) :
    map (ExactFunctor.whiskerRight α G) ≫
        (compFunctorIso F' G).hom =
      (compFunctorIso F G).hom ≫
        Functor.whiskerRight (map α) (functor G) := sorry

/-- The bounded-above composition comparison is natural in its second exact
functor. -/
@[reassoc]
theorem compFunctorIso.naturality_right
    (F : A ⥤ₑ B) {G G' : B ⥤ₑ C} (β : G ⟶ G') :
    map (ExactFunctor.whiskerLeft F β) ≫
        (compFunctorIso F G').hom =
      (compFunctorIso F G).hom ≫
        Functor.whiskerLeft (functor F) (map β) := sorry

/-- The inverse bounded-above composition comparison is natural in its
first exact functor. -/
@[reassoc]
theorem compFunctorIso.inv_naturality_left
    {F F' : A ⥤ₑ B} (α : F ⟶ F') (G : B ⥤ₑ C) :
    Functor.whiskerRight (map α) (functor G) ≫
        (compFunctorIso F' G).inv =
      (compFunctorIso F G).inv ≫
        map (ExactFunctor.whiskerRight α G) := sorry

/-- The inverse bounded-above composition comparison is natural in its
second exact functor. -/
@[reassoc]
theorem compFunctorIso.inv_naturality_right
    (F : A ⥤ₑ B) {G G' : B ⥤ₑ C} (β : G ⟶ G') :
    Functor.whiskerLeft (functor F) (map β) ≫
        (compFunctorIso F G').inv =
      (compFunctorIso F G).inv ≫
        map (ExactFunctor.whiskerLeft F β) := sorry

end Minus

namespace Bounded

/-- The bounded composition comparison is natural in both exact functors. -/
@[reassoc, stacks 015F "naturality of bounded exact-derived composition"]
theorem compFunctorIso.naturality
    {F F' : A ⥤ₑ B} (α : F ⟶ F') {G G' : B ⥤ₑ C} (β : G ⟶ G') :
    map (ExactFunctor.hcomp α β) ≫ (compFunctorIso F' G').hom =
      (compFunctorIso F G).hom ≫
        NatTrans.hcomp (map α) (map β) := sorry

/-- The inverse bounded composition comparison is natural in both exact
functors. -/
@[reassoc]
theorem compFunctorIso.inv_naturality
    {F F' : A ⥤ₑ B} (α : F ⟶ F') {G G' : B ⥤ₑ C} (β : G ⟶ G') :
    NatTrans.hcomp (map α) (map β) ≫
        (compFunctorIso F' G').inv =
      (compFunctorIso F G).inv ≫
        map (ExactFunctor.hcomp α β) := sorry

/-- The bounded composition comparison is natural in its first exact
functor. -/
@[reassoc]
theorem compFunctorIso.naturality_left
    {F F' : A ⥤ₑ B} (α : F ⟶ F') (G : B ⥤ₑ C) :
    map (ExactFunctor.whiskerRight α G) ≫
        (compFunctorIso F' G).hom =
      (compFunctorIso F G).hom ≫
        Functor.whiskerRight (map α) (functor G) := sorry

/-- The bounded composition comparison is natural in its second exact
functor. -/
@[reassoc]
theorem compFunctorIso.naturality_right
    (F : A ⥤ₑ B) {G G' : B ⥤ₑ C} (β : G ⟶ G') :
    map (ExactFunctor.whiskerLeft F β) ≫
        (compFunctorIso F G').hom =
      (compFunctorIso F G).hom ≫
        Functor.whiskerLeft (functor F) (map β) := sorry

/-- The inverse bounded composition comparison is natural in its first
exact functor. -/
@[reassoc]
theorem compFunctorIso.inv_naturality_left
    {F F' : A ⥤ₑ B} (α : F ⟶ F') (G : B ⥤ₑ C) :
    Functor.whiskerRight (map α) (functor G) ≫
        (compFunctorIso F' G).inv =
      (compFunctorIso F G).inv ≫
        map (ExactFunctor.whiskerRight α G) := sorry

/-- The inverse bounded composition comparison is natural in its second
exact functor. -/
@[reassoc]
theorem compFunctorIso.inv_naturality_right
    (F : A ⥤ₑ B) {G G' : B ⥤ₑ C} (β : G ⟶ G') :
    Functor.whiskerLeft (functor F) (map β) ≫
        (compFunctorIso F G').inv =
      (compFunctorIso F G).inv ≫
        map (ExactFunctor.whiskerLeft F β) := sorry

end Bounded

end CategoryTheory.ExactFunctor.Derived
