/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.IndexedFunctor.Fiberwise
public import ReasLib.CategoryTheory.Fibered.CategoricalPullback.Fiber.Equivalence
public import ReasLib.CategoryTheory.Fibered.CategoricalPullback.Reindex.Explicit.Naturality
public import ReasLib.CategoryTheory.Fibered.Cleavage.Pseudofunctor.Construction

/-!
# Explicit indexed fiber comparison for a categorical pullback

For a specified cleavage on the right leg, the first projection of a
categorical pullback induces a fiberwise equivalence compatible with every
reindexing functor. This is the choice-explicit owner of that indexed
comparison. The selected-cleavage and canonical-pseudofunctor specializations
are layered in sibling modules.
-/

@[expose] public section

open CategoryTheory.Limits
open CategoricalPullback
open scoped CategoricalPullback

universe uC uD uS vC vD vS

namespace CategoryTheory

open Functor Opposite
open scoped CategoryTheory.Bicategory

namespace Limits.CategoricalPullback.Indexed.explicit

variable {C : Type uC} {D : Type uD} {S : Type uS}
variable [Category.{vC} C] [Category.{vD} D] [Category.{vS} S]

/-- Identity coherence for the indexed fiber comparison associated with an explicit cleavage. -/
theorem functor.naturality.id.hom
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage)
    (U : C) (X : (π₁ u p).Fiber U) :
    (Fiber.forward.functor u p χ U).map
          (((χ.ofRight u).toPseudofunctor.mapIdOp U).inv.toNatTrans.app X) ≫
        (Reindex.explicit.comparisonNatIso u p χ (𝟙 U)).hom.app X =
      (χ.toPseudofunctor.mapIdOp'
        (u.obj U) (u.map (𝟙 U)) (u.map_id U)).inv.toNatTrans.app
          ((Fiber.forward.functor u p χ U).obj X) := sorry

/-- Inverse identity coherence for the indexed fiber comparison associated with an explicit
cleavage. -/
theorem functor.naturality.id.inv
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage)
    (U : C) (X : (π₁ u p).Fiber U) :
    (Reindex.explicit.comparisonNatIso u p χ (𝟙 U)).inv.app X ≫
        (Fiber.forward.functor u p χ U).map
          (((χ.ofRight u).toPseudofunctor.mapIdOp U).hom.toNatTrans.app X) =
      (χ.toPseudofunctor.mapIdOp'
        (u.obj U) (u.map (𝟙 U)) (u.map_id U)).hom.toNatTrans.app
          ((Fiber.forward.functor u p χ U).obj X) := sorry

/-- Composition coherence for the indexed fiber comparison associated with an explicit
cleavage. -/
theorem functor.naturality.comp.hom
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (X : (π₁ u p).Fiber U) :
    (Reindex.explicit.comparisonNatIso u p χ (g ≫ f)).hom.app X ≫
        (χ.toPseudofunctor.mapCompOp'
          (u.map f) (u.map g) (u.map (g ≫ f))
          (u.map_comp g f).symm).hom.toNatTrans.app
            ((Fiber.forward.functor u p χ U).obj X) =
      (Fiber.forward.functor u p χ W).map
          (((χ.ofRight u).toPseudofunctor.mapCompOp f g).hom.toNatTrans.app X) ≫
        (Reindex.explicit.comparisonNatIso u p χ g).hom.app
          (((χ.ofRight u).toPseudofunctor.map
            f.op.toLoc).toFunctor.obj X) ≫
        (χ.toPseudofunctor.map (u.map g).op.toLoc).toFunctor.map
          ((Reindex.explicit.comparisonNatIso u p χ f).hom.app X) := sorry

/-- Inverse composition coherence for the indexed fiber comparison associated with an explicit
cleavage. -/
theorem functor.naturality.comp.inv
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (X : (π₁ u p).Fiber U) :
    (χ.toPseudofunctor.map (u.map g).op.toLoc).toFunctor.map
          ((Reindex.explicit.comparisonNatIso u p χ f).inv.app X) ≫
        (Reindex.explicit.comparisonNatIso u p χ g).inv.app
          (((χ.ofRight u).toPseudofunctor.map
            f.op.toLoc).toFunctor.obj X) ≫
        (Fiber.forward.functor u p χ W).map
          (((χ.ofRight u).toPseudofunctor.mapCompOp f g).inv.toNatTrans.app X) =
      (χ.toPseudofunctor.mapCompOp'
          (u.map f) (u.map g) (u.map (g ≫ f))
          (u.map_comp g f).symm).inv.toNatTrans.app
            ((Fiber.forward.functor u p χ U).obj X) ≫
        (Reindex.explicit.comparisonNatIso u p χ (g ≫ f)).inv.app X := sorry

/-- The fiber comparison for a categorical pullback, together with its coherent compatibility
with all reindexing functors. -/
noncomputable def functor
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage) :
    Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor u
      (χ.ofRight u).toPseudofunctor χ.toPseudofunctor where
  app U := Fiber.forward.functor u p χ U
  naturality f := Reindex.explicit.comparisonNatIso u p χ f
  naturality_id U X := functor.naturality.id.hom u p χ U X
  naturality_comp f g X := functor.naturality.comp.hom u p χ f g X

/-- The component of the explicit indexed comparison is the explicit fiber functor. -/
@[simp]
theorem functor.app
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage) (U : C) :
    (functor u p χ).app U = Fiber.forward.functor u p χ U := sorry

/-- The naturality isomorphism of the explicit indexed comparison is the explicit reindexing
comparison. -/
@[simp]
theorem functor.naturality
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage)
    {U V : C} (f : V ⟶ U) :
    (functor u p χ).naturality f =
      Reindex.explicit.comparisonNatIso u p χ f := sorry

/-- Forward naturality component of the explicit indexed comparison. -/
@[simp]
theorem functor.naturality.hom.app
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage)
    {U V : C} (f : V ⟶ U) (X : (π₁ u p).Fiber U) :
    ((functor u p χ).naturality f).hom.app X =
      (Reindex.explicit.comparisonIso u p χ f X).hom := sorry

/-- Inverse naturality component of the explicit indexed comparison. -/
@[simp]
theorem functor.naturality.inv.app
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage)
    {U V : C} (f : V ⟶ U) (X : (π₁ u p).Fiber U) :
    ((functor u p χ).naturality f).inv.app X =
      (Reindex.explicit.comparisonIso u p χ f X).inv := sorry

/-- Restricted-morphism transport through the explicit indexed comparison. -/
@[simp]
theorem functor.mapHom
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage)
    {U₁ U₂ V : C} (f₁ : V ⟶ U₁) (f₂ : V ⟶ U₂)
    {X : (π₁ u p).Fiber U₁} {Y : (π₁ u p).Fiber U₂}
    (φ :
      (((χ.ofRight u).toPseudofunctor.map
        f₁.op.toLoc).toFunctor.obj X) ⟶
      (((χ.ofRight u).toPseudofunctor.map
        f₂.op.toLoc).toFunctor.obj Y)) :
    (functor u p χ).mapHom f₁ f₂ φ =
      (Reindex.explicit.comparisonNatIso u p χ f₁).inv.app X ≫
        (Fiber.forward.functor u p χ V).map φ ≫
        (Reindex.explicit.comparisonNatIso u p χ f₂).hom.app Y := sorry

/-- Total-category readout of restricted-morphism transport through the explicit indexed
comparison. -/
theorem functor.mapHom.toTotal
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage)
    {U₁ U₂ V : C} (f₁ : V ⟶ U₁) (f₂ : V ⟶ U₂)
    {X : (π₁ u p).Fiber U₁} {Y : (π₁ u p).Fiber U₂}
    (φ :
      (((χ.ofRight u).toPseudofunctor.map
        f₁.op.toLoc).toFunctor.obj X) ⟶
      (((χ.ofRight u).toPseudofunctor.map
        f₂.op.toLoc).toFunctor.obj Y)) :
    ((functor u p χ).mapHom f₁ f₂ φ).1 =
      ((Reindex.explicit.comparisonNatIso u p χ f₁).inv.app X).1 ≫
        ((Fiber.forward.functor u p χ V).map φ).1 ≫
        ((Reindex.explicit.comparisonNatIso u p χ f₂).hom.app Y).1 := sorry

/-- The explicit indexed comparison is an equivalence on every fiber. -/
instance functor.fiberwiseEquivalence
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage) :
    (functor u p χ).FiberwiseEquivalence := sorry

end Limits.CategoricalPullback.Indexed.explicit

end CategoryTheory
