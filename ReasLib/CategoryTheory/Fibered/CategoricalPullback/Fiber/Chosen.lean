/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.CategoricalPullback.Fiber.Equivalence
public import ReasLib.CategoryTheory.Fibered.ChosenCleavage.Basic

/-!
# Chosen-cleavage comparison of categorical-pullback fibers

This is the application-facing specialization of the explicit fiber comparison
to `Functor.Cleavage.ofIsFibered`.  The cleavage-explicit modules remain the
canonical owners of its concrete construction and coherence data.
-/

@[expose] public section

open CategoryTheory.Limits
open CategoricalPullback
open scoped CategoricalPullback

universe uC uD uS vC vD vS

namespace CategoryTheory

open Functor

namespace Limits.CategoricalPullback

variable {C : Type uC} {D : Type uD} {S : Type uS}
variable [Category.{vC} C] [Category.{vD} D] [Category.{vS} S]

/-- The selected fiber comparison obtained from mathlib's chosen cleavage on a fibred right
leg.  This is a convenience surface; `Fiber.forward.functor` remains the choice-explicit
owner. -/
noncomputable def Fiber.chosen.functor
    (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered] (U : C) :
    (π₁ u p).Fiber U ⥤ p.Fiber (u.obj U) :=
  Fiber.forward.functor u p (Cleavage.ofIsFibered p) U

/-- Objectwise computation for the selected pullback-fiber comparison. -/
@[simp]
theorem Fiber.chosen.functor.obj
    (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered] (U : C)
    (X : (π₁ u p).Fiber U) :
    (Fiber.chosen.functor u p U).obj X =
      Fiber.forward.strict u p (Cleavage.ofIsFibered p) X := sorry

/-- Morphismwise computation for the selected pullback-fiber comparison. -/
@[simp]
theorem Fiber.chosen.functor.map
    (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered] (U : C)
    {X Y : (π₁ u p).Fiber U} (φ : X ⟶ Y) :
    (Fiber.chosen.functor u p U).map φ =
      Fiber.forward.map u p (Cleavage.ofIsFibered p) φ := sorry

/-- The selected pullback-fiber comparison is an equivalence. -/
instance Fiber.chosen.functor.isEquivalence
    (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered] (U : C) :
    (Fiber.chosen.functor u p U).IsEquivalence := sorry

/-- For a fibred right leg, the strict right-fiber embedding is canonically available as an
equivalence functor. -/
instance Fiber.chosen.inverse.isEquivalence
    (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered] (U : C) :
    (Fiber.reverse.functor u p U).IsEquivalence := sorry

/-- The selected equivalence between a fiber of a categorical-pullback projection and the
corresponding fiber of its right leg. -/
noncomputable def Fiber.chosen.equivalence
    (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered] (U : C) :
    (π₁ u p).Fiber U ≌ p.Fiber (u.obj U) :=
  Fiber.equivalence u p (Cleavage.ofIsFibered p) U

/-- The forward functor of the selected fiber equivalence is the selected comparison functor. -/
@[simp]
theorem Fiber.chosen.equivalence.functor
    (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered] (U : C) :
    (Fiber.chosen.equivalence u p U).functor =
      Fiber.chosen.functor u p U := sorry

/-- The inverse functor of the selected fiber equivalence is the strict right-fiber embedding. -/
@[simp]
theorem Fiber.chosen.equivalence.inverse
    (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered] (U : C) :
    (Fiber.chosen.equivalence u p U).inverse =
      Fiber.reverse.functor u p U := sorry

/-- The inverse unit component of the selected fiber equivalence is the explicit pullback-fiber
comparison map. -/
@[simp]
theorem Fiber.chosen.equivalence.unitIso.inv.app
    (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered] (U : C)
    (X : (π₁ u p).Fiber U) :
    (Fiber.chosen.equivalence u p U).unitIso.inv.app X =
      Fiber.equivalence.inverseUnit.hom u p (Cleavage.ofIsFibered p) X := sorry

/-- The forward unit component of the selected fiber equivalence is the inverse explicit
pullback-fiber comparison. -/
@[simp]
theorem Fiber.chosen.equivalence.unitIso.hom.app
    (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered] (U : C)
    (X : (π₁ u p).Fiber U) :
    (Fiber.chosen.equivalence u p U).unitIso.hom.app X =
      (Fiber.equivalence.inverseUnit.app
        u p (Cleavage.ofIsFibered p) X).inv := sorry

/-- The counit component of the selected fiber equivalence is the selected strictification
map. -/
@[simp]
theorem Fiber.chosen.equivalence.counitIso.hom.app
    (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered] (U : C)
    (X : p.Fiber (u.obj U)) :
    (Fiber.chosen.equivalence u p U).counitIso.hom.app X =
      Fiber.equivalence.counit.hom u p (Cleavage.ofIsFibered p) X := sorry

/-- The inverse counit component of the selected fiber equivalence is the inverse selected
strictification isomorphism. -/
@[simp]
theorem Fiber.chosen.equivalence.counitIso.inv.app
    (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered] (U : C)
    (X : p.Fiber (u.obj U)) :
    (Fiber.chosen.equivalence u p U).counitIso.inv.app X =
      (Fiber.equivalence.counit.app
        u p (Cleavage.ofIsFibered p) X).inv := sorry

end Limits.CategoricalPullback

end CategoryTheory
