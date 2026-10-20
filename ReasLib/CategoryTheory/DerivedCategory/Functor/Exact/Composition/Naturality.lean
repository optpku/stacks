/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Composition
public import ReasLib.CategoryTheory.Functor.Exactness.Composition.Naturality
import Mathlib.Tactic.CrossRefAttribute

/-!
# Naturality of exact-derived composition comparisons

The canonical comparison between the derived functor of a composite and the
composite of the derived functors is natural in both exact functors.  This
file exposes the two-variable square together with its common one-variable
specializations.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe w₁ w₂ w₃ v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.ExactFunctor.MapDerivedCategory

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]
variable {C : Type u₃} [Category.{v₃} C] [Abelian C] [HasDerivedCategory.{w₃} C]

namespace compFunctorIso

/-- The forward exact-derived composition comparison is natural in both
exact functors. -/
@[reassoc, stacks 015F "naturality of exact-derived composition"]
theorem naturality
    {F F' : A ⥤ₑ B} (α : F ⟶ F') {G G' : B ⥤ₑ C} (β : G ⟶ G') :
    map (ExactFunctor.hcomp α β) ≫ (compFunctorIso F' G').hom =
      (compFunctorIso F G).hom ≫ NatTrans.hcomp (map α) (map β) := sorry

/-- The inverse exact-derived composition comparison is natural in both
exact functors. -/
@[reassoc, stacks 015F "inverse naturality of exact-derived composition"]
theorem inv_naturality
    {F F' : A ⥤ₑ B} (α : F ⟶ F') {G G' : B ⥤ₑ C} (β : G ⟶ G') :
    NatTrans.hcomp (map α) (map β) ≫ (compFunctorIso F' G').inv =
      (compFunctorIso F G).inv ≫ map (ExactFunctor.hcomp α β) := sorry

/-- The forward exact-derived composition comparison is natural in its
first exact functor. -/
@[reassoc]
theorem naturality_left
    {F F' : A ⥤ₑ B} (α : F ⟶ F') (G : B ⥤ₑ C) :
    map (ExactFunctor.whiskerRight α G) ≫ (compFunctorIso F' G).hom =
      (compFunctorIso F G).hom ≫
        Functor.whiskerRight (map α) G.mapDerivedCategory := sorry

/-- The forward exact-derived composition comparison is natural in its
second exact functor. -/
@[reassoc]
theorem naturality_right
    (F : A ⥤ₑ B) {G G' : B ⥤ₑ C} (β : G ⟶ G') :
    map (ExactFunctor.whiskerLeft F β) ≫ (compFunctorIso F G').hom =
      (compFunctorIso F G).hom ≫
        Functor.whiskerLeft F.mapDerivedCategory (map β) := sorry

/-- The inverse exact-derived composition comparison is natural in its
first exact functor. -/
@[reassoc]
theorem inv_naturality_left
    {F F' : A ⥤ₑ B} (α : F ⟶ F') (G : B ⥤ₑ C) :
    Functor.whiskerRight (map α) G.mapDerivedCategory ≫
        (compFunctorIso F' G).inv =
      (compFunctorIso F G).inv ≫
        map (ExactFunctor.whiskerRight α G) := sorry

/-- The inverse exact-derived composition comparison is natural in its
second exact functor. -/
@[reassoc]
theorem inv_naturality_right
    (F : A ⥤ₑ B) {G G' : B ⥤ₑ C} (β : G ⟶ G') :
    Functor.whiskerLeft F.mapDerivedCategory (map β) ≫
        (compFunctorIso F G').inv =
      (compFunctorIso F G).inv ≫
        map (ExactFunctor.whiskerLeft F β) := sorry

end compFunctorIso

end CategoryTheory.ExactFunctor.MapDerivedCategory
