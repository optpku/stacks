/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.CategoricalPullback.Fiber.Chosen
public import ReasLib.CategoryTheory.Fibered.CategoricalPullback.Reindex.Explicit.Naturality
public import ReasLib.CategoryTheory.Fibered.ChosenCleavage.Basic

/-!
# Chosen reindexing comparison for categorical-pullback fibers

This is the `Functor.IsFibered` specialization of the explicit reindexing
comparison. The explicit module remains the canonical owner of the concrete
cartesian construction and choice-free coherence data.
-/

@[expose] public section

open CategoryTheory.Limits
open CategoricalPullback
open scoped CategoricalPullback

universe uC uD uS vC vD vS

namespace CategoryTheory

open Functor

namespace Limits.CategoricalPullback.Reindex.chosen

variable {C : Type uC} {D : Type uD} {S : Type uS}
variable [Category.{vC} C] [Category.{vD} D] [Category.{vS} S]

/-- The selected objectwise identity comparison for pullback-fiber reindexing. -/
noncomputable def idIsoApp
    (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered]
    (U : C) (X : (π₁ u p).Fiber U) :
    X ≅ (Cleavage.chosen.reindex u p (𝟙 U)).obj X :=
  Cleavage.Reindex.idIsoApp (Cleavage.chosen u p) U X

/-- The selected objectwise composition comparison for pullback-fiber reindexing. -/
noncomputable def compIsoApp
    (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered]
    {U V W : C} (a : V ⟶ U) (b : W ⟶ V)
    (X : (π₁ u p).Fiber U) :
    (Cleavage.chosen.reindex u p (b ≫ a)).obj X ≅
      (Cleavage.chosen.reindex u p b).obj
        ((Cleavage.chosen.reindex u p a).obj X) :=
  Cleavage.Reindex.compIsoApp (Cleavage.chosen u p) a b X

/-- The selected identity comparisons for the induced pullback cleavage assemble naturally. -/
noncomputable def idIso
    (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered] (U : C) :
    𝟭 ((π₁ u p).Fiber U) ≅ Cleavage.chosen.reindex u p (𝟙 U) :=
  Cleavage.Reindex.idIso (Cleavage.chosen u p) U

/-- The selected composition comparisons for the induced pullback cleavage assemble naturally. -/
noncomputable def compIso
    (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered]
    {U V W : C} (a : V ⟶ U) (b : W ⟶ V) :
    Cleavage.chosen.reindex u p (b ≫ a) ≅
      Cleavage.chosen.reindex u p a ⋙
        Cleavage.chosen.reindex u p b :=
  Cleavage.Reindex.compIso (Cleavage.chosen u p) a b

/-- The forward component of the selected identity comparison is the selected objectwise
identity comparison. -/
@[simp]
theorem idIso.hom.app
    (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered]
    (U : C) (X : (π₁ u p).Fiber U) :
    (idIso u p U).hom.app X = (idIsoApp u p U X).hom := sorry

/-- The inverse component of the selected identity comparison is the inverse selected
objectwise identity comparison. -/
@[simp]
theorem idIso.inv.app
    (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered]
    (U : C) (X : (π₁ u p).Fiber U) :
    (idIso u p U).inv.app X = (idIsoApp u p U X).inv := sorry

/-- The forward component of the selected composition comparison is the selected objectwise
composition comparison. -/
@[simp]
theorem compIso.hom.app
    (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered]
    {U V W : C} (a : V ⟶ U) (b : W ⟶ V)
    (X : (π₁ u p).Fiber U) :
    (compIso u p a b).hom.app X = (compIsoApp u p a b X).hom := sorry

/-- The inverse component of the selected composition comparison is the inverse selected
objectwise composition comparison. -/
@[simp]
theorem compIso.inv.app
    (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered]
    {U V W : C} (a : V ⟶ U) (b : W ⟶ V)
    (X : (π₁ u p).Fiber U) :
    (compIso u p a b).inv.app X = (compIsoApp u p a b X).inv := sorry

/-- Selected compatibility of pullback-fiber comparison with reindexing. Both source and target
reindexing choices are induced from the same selected cleavage on `p`. -/
noncomputable def comparisonNatIso
    (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered]
    {U V : C} (a : V ⟶ U) :
    Cleavage.chosen.reindex u p a ⋙
        Fiber.chosen.functor u p V ≅
      Fiber.chosen.functor u p U ⋙ Chosen.reindex p (u.map a) :=
  Reindex.explicit.comparisonNatIso u p (Cleavage.ofIsFibered p) a

/-- Forward component of the selected reindexing comparison. -/
@[simp]
theorem comparisonNatIso.hom.app
    (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered]
    {U V : C} (a : V ⟶ U) (X : (π₁ u p).Fiber U) :
    (comparisonNatIso u p a).hom.app X =
      (Reindex.explicit.comparisonIso
        u p (Cleavage.ofIsFibered p) a X).hom := sorry

/-- Inverse component of the selected reindexing comparison. -/
@[simp]
theorem comparisonNatIso.inv.app
    (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered]
    {U V : C} (a : V ⟶ U) (X : (π₁ u p).Fiber U) :
    (comparisonNatIso u p a).inv.app X =
      (Reindex.explicit.comparisonIso
        u p (Cleavage.ofIsFibered p) a X).inv := sorry

/-- Mapping selected pullback-fiber reindexing through the comparison into the right fiber. -/
theorem comparisonNatIso.map.toRight
    (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered]
    {U V : C} (a : V ⟶ U)
    {X Y : (π₁ u p).Fiber U} (φ : X ⟶ Y) :
    (Fiber.chosen.functor u p V).map
        (Cleavage.chosen.reindexMap u p a φ) =
      (comparisonNatIso u p a).hom.app X ≫
        (Chosen.reindex p (u.map a)).map
          ((Fiber.chosen.functor u p U).map φ) ≫
        (comparisonNatIso u p a).inv.app Y := sorry

/-- Total-category readout of `comparisonNatIso.map.toRight`. -/
theorem comparisonNatIso.map.toRight.toTotal
    (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered]
    {U V : C} (a : V ⟶ U)
    {X Y : (π₁ u p).Fiber U} (φ : X ⟶ Y) :
    ((Fiber.chosen.functor u p V).map
        (Cleavage.chosen.reindexMap u p a φ)).1 =
      ((comparisonNatIso u p a).hom.app X).1 ≫
        ((Chosen.reindex p (u.map a)).map
          ((Fiber.chosen.functor u p U).map φ)).1 ≫
        ((comparisonNatIso u p a).inv.app Y).1 := sorry

/-- Reindexing a right-fiber comparison map back through the selected pullback fiber. -/
theorem comparisonNatIso.map.fromRight
    (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered]
    {U V : C} (a : V ⟶ U)
    {X Y : (π₁ u p).Fiber U} (φ : X ⟶ Y) :
    (Chosen.reindex p (u.map a)).map
        ((Fiber.chosen.functor u p U).map φ) =
      (comparisonNatIso u p a).inv.app X ≫
        (Fiber.chosen.functor u p V).map
          (Cleavage.chosen.reindexMap u p a φ) ≫
        (comparisonNatIso u p a).hom.app Y := sorry

/-- Total-category readout of `comparisonNatIso.map.fromRight`. -/
theorem comparisonNatIso.map.fromRight.toTotal
    (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered]
    {U V : C} (a : V ⟶ U)
    {X Y : (π₁ u p).Fiber U} (φ : X ⟶ Y) :
    ((Chosen.reindex p (u.map a)).map
        ((Fiber.chosen.functor u p U).map φ)).1 =
      ((comparisonNatIso u p a).inv.app X).1 ≫
        ((Fiber.chosen.functor u p V).map
          (Cleavage.chosen.reindexMap u p a φ)).1 ≫
        ((comparisonNatIso u p a).hom.app Y).1 := sorry

/-- The forward identity coherence boundary for the selected comparison. -/
theorem comparisonNatIso.id.hom
    (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered]
    (U : C) (X : (π₁ u p).Fiber U) :
    (Fiber.chosen.functor u p U).map (idIsoApp u p U X).hom ≫
        (comparisonNatIso u p (𝟙 U)).hom.app X ≫
        (Chosen.Reindex.congrIsoApp p (u.map_id U)
          ((Fiber.chosen.functor u p U).obj X)).hom =
      (Chosen.Reindex.idIsoApp p (u.obj U)
        ((Fiber.chosen.functor u p U).obj X)).hom := sorry

/-- The inverse identity coherence boundary for the selected comparison. -/
theorem comparisonNatIso.id.inv
    (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered]
    (U : C) (X : (π₁ u p).Fiber U) :
    (Chosen.Reindex.idIsoApp p (u.obj U)
          ((Fiber.chosen.functor u p U).obj X)).inv =
      (Chosen.Reindex.congrIsoApp p (u.map_id U)
          ((Fiber.chosen.functor u p U).obj X)).inv ≫
        (comparisonNatIso u p (𝟙 U)).inv.app X ≫
        (Fiber.chosen.functor u p U).map (idIsoApp u p U X).inv := sorry

/-- The forward composition coherence boundary for the selected comparison. -/
theorem comparisonNatIso.comp.hom
    (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered]
    {U V W : C} (a : V ⟶ U) (b : W ⟶ V)
    (X : (π₁ u p).Fiber U) :
    (comparisonNatIso u p (b ≫ a)).hom.app X ≫
        (Chosen.Reindex.specifiedCompIsoApp p (u.map a) (u.map b)
          (u.map (b ≫ a)) (u.map_comp b a).symm
          ((Fiber.chosen.functor u p U).obj X)).hom =
      (Fiber.chosen.functor u p W).map (compIsoApp u p a b X).hom ≫
        (comparisonNatIso u p b).hom.app
          ((Cleavage.chosen.reindex u p a).obj X) ≫
        (Chosen.reindex p (u.map b)).map
          ((comparisonNatIso u p a).hom.app X) := sorry

/-- The inverse composition coherence boundary for the selected comparison. -/
theorem comparisonNatIso.comp.inv
    (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered]
    {U V W : C} (a : V ⟶ U) (b : W ⟶ V)
    (X : (π₁ u p).Fiber U) :
    (Chosen.Reindex.specifiedCompIsoApp p (u.map a) (u.map b)
          (u.map (b ≫ a)) (u.map_comp b a).symm
          ((Fiber.chosen.functor u p U).obj X)).inv ≫
        (comparisonNatIso u p (b ≫ a)).inv.app X =
      (Chosen.reindex p (u.map b)).map
          ((comparisonNatIso u p a).inv.app X) ≫
        (comparisonNatIso u p b).inv.app
          ((Cleavage.chosen.reindex u p a).obj X) ≫
        (Fiber.chosen.functor u p W).map (compIsoApp u p a b X).inv := sorry

end Limits.CategoricalPullback.Reindex.chosen

end CategoryTheory
