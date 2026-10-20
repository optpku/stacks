/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.CategoricalPullback.Reindex.Explicit.Construction

/-!
# Naturality of the explicit categorical-pullback reindexing comparison

This module assembles the objectwise cartesian comparison into a natural
isomorphism and records the two conjugation formulas needed to transport
reindexed fiber morphisms.
-/

@[expose] public section

open CategoryTheory.Limits
open CategoricalPullback
open scoped CategoricalPullback

universe uC uD uS vC vD vS

namespace CategoryTheory

open Functor

namespace Limits.CategoricalPullback.Reindex.explicit

variable {C : Type uC} {D : Type uD} {S : Type uS}
variable [Category.{vC} C] [Category.{vD} D] [Category.{vS} S]

/-- The objectwise reindexing comparison is natural in the pullback-fiber object. -/
theorem comparisonIso.naturality.hom
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage)
    {U V : C} (a : V ⟶ U)
    {X Y : (π₁ u p).Fiber U} (φ : X ⟶ Y) :
    ((χ.ofRight u).reindex a ⋙
        Fiber.forward.functor u p χ V).map φ ≫
      (comparisonIso u p χ a Y).hom =
    (comparisonIso u p χ a X).hom ≫
      (Fiber.forward.functor u p χ U ⋙
        χ.reindex (u.map a)).map φ := sorry

/-- Inverse naturality of the objectwise reindexing comparison. -/
theorem comparisonIso.naturality.inv
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage)
    {U V : C} (a : V ⟶ U)
    {X Y : (π₁ u p).Fiber U} (φ : X ⟶ Y) :
    (Fiber.forward.functor u p χ U ⋙
        χ.reindex (u.map a)).map φ ≫
      (comparisonIso u p χ a Y).inv =
    (comparisonIso u p χ a X).inv ≫
      ((χ.ofRight u).reindex a ⋙
        Fiber.forward.functor u p χ V).map φ := sorry

/-- The objectwise comparisons assemble into a natural isomorphism expressing compatibility of
the pullback-fiber equivalence with reindexing. -/
noncomputable def comparisonNatIso
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage)
    {U V : C} (a : V ⟶ U) :
    (χ.ofRight u).reindex a ⋙
        Fiber.forward.functor u p χ V ≅
      Fiber.forward.functor u p χ U ⋙ χ.reindex (u.map a) :=
  NatIso.ofComponents (comparisonIso u p χ a)
    (fun φ ↦ comparisonIso.naturality.hom u p χ a φ)

/-- The forward component of the natural reindexing comparison is the explicit componentwise
comparison. -/
@[simp]
theorem comparisonNatIso.hom.app
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage)
    {U V : C} (a : V ⟶ U) (X : (π₁ u p).Fiber U) :
    (comparisonNatIso u p χ a).hom.app X =
      (comparisonIso u p χ a X).hom := sorry

/-- The inverse component of the natural reindexing comparison is the explicit componentwise
comparison inverse. -/
@[simp]
theorem comparisonNatIso.inv.app
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage)
    {U V : C} (a : V ⟶ U) (X : (π₁ u p).Fiber U) :
    (comparisonNatIso u p χ a).inv.app X =
      (comparisonIso u p χ a X).inv := sorry

/-- Mapping a reindexed pullback-fiber morphism through the fiber comparison is conjugation of
the reindexed right-fiber morphism by the two comparison components. -/
theorem comparisonNatIso.map.toRight
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage)
    {U V : C} (a : V ⟶ U)
    {X Y : (π₁ u p).Fiber U} (φ : X ⟶ Y) :
    (Fiber.forward.functor u p χ V).map
        ((χ.ofRight u).reindexMap a φ) =
      (comparisonIso u p χ a X).hom ≫
        (χ.reindex (u.map a)).map
          ((Fiber.forward.functor u p χ U).map φ) ≫
        (comparisonIso u p χ a Y).inv := sorry

/-- Total-category readout of mapping a reindexed morphism through the pullback-fiber
comparison. -/
theorem comparisonNatIso.map.toRight.toTotal
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage)
    {U V : C} (a : V ⟶ U)
    {X Y : (π₁ u p).Fiber U} (φ : X ⟶ Y) :
    ((Fiber.forward.functor u p χ V).map
        ((χ.ofRight u).reindexMap a φ)).1 =
      (comparisonIso u p χ a X).hom.1 ≫
        ((χ.reindex (u.map a)).map
          ((Fiber.forward.functor u p χ U).map φ)).1 ≫
        (comparisonIso u p χ a Y).inv.1 := sorry

/-- Reindexing a right-fiber comparison map is conjugation of the mapped pullback-fiber
reindexing by the inverse comparison components. -/
theorem comparisonNatIso.map.fromRight
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage)
    {U V : C} (a : V ⟶ U)
    {X Y : (π₁ u p).Fiber U} (φ : X ⟶ Y) :
    (χ.reindex (u.map a)).map
        ((Fiber.forward.functor u p χ U).map φ) =
      (comparisonIso u p χ a X).inv ≫
        (Fiber.forward.functor u p χ V).map
          ((χ.ofRight u).reindexMap a φ) ≫
        (comparisonIso u p χ a Y).hom := sorry

/-- Total-category readout of reindexing a morphism mapped through the pullback-fiber
comparison. -/
theorem comparisonNatIso.map.fromRight.toTotal
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage)
    {U V : C} (a : V ⟶ U)
    {X Y : (π₁ u p).Fiber U} (φ : X ⟶ Y) :
    ((χ.reindex (u.map a)).map
        ((Fiber.forward.functor u p χ U).map φ)).1 =
      (comparisonIso u p χ a X).inv.1 ≫
        ((Fiber.forward.functor u p χ V).map
          ((χ.ofRight u).reindexMap a φ)).1 ≫
        (comparisonIso u p χ a Y).hom.1 := sorry

end Limits.CategoricalPullback.Reindex.explicit

end CategoryTheory
