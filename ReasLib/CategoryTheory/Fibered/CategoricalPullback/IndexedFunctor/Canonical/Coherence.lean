module

public import ReasLib.CategoryTheory.Fibered.CategoricalPullback.IndexedFunctor.Canonical.Basic

/-!
# Coherence for the canonical indexed pullback-fiber comparison

The canonical restriction isomorphism is a component of an indexed functor.
This leaf exposes its identity and composition boundaries in the concrete
fiber language used by downstream descent and transport arguments.
-/

@[expose] public section

open CategoryTheory.Limits
open CategoricalPullback
open scoped CategoricalPullback

universe uC uD uS vC vD vS

namespace CategoryTheory

open Functor Opposite
open scoped CategoryTheory.Bicategory

namespace Limits.CategoricalPullback

variable {C : Type uC} {D : Type uD} {S : Type uS}
variable [Category.{vC} C] [Category.{vD} D] [Category.{vS} S]

/-- Naturality of the forward canonical restriction comparison in a pullback-fiber morphism. -/
@[reassoc]
theorem Indexed.canonical.comparisonIso.naturality.hom
    (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered]
    {U V : C} (f : V ⟶ U)
    {X Y : (π₁ u p).Fiber U} (φ : X ⟶ Y) :
    (Fiber.chosen.functor u p V).map
          (((fiberPseudofunctor (π₁ u p)).map
            f.op.toLoc).toFunctor.map φ) ≫
        (Indexed.canonical.comparisonIso u p f Y).hom =
      (Indexed.canonical.comparisonIso u p f X).hom ≫
        ((fiberPseudofunctor p).map
          (u.map f).op.toLoc).toFunctor.map
            ((Fiber.chosen.functor u p U).map φ) := sorry

/-- Naturality of the inverse canonical restriction comparison in a pullback-fiber morphism. -/
@[reassoc]
theorem Indexed.canonical.comparisonIso.naturality.inv
    (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered]
    {U V : C} (f : V ⟶ U)
    {X Y : (π₁ u p).Fiber U} (φ : X ⟶ Y) :
    (Indexed.canonical.comparisonIso u p f X).inv ≫
        (Fiber.chosen.functor u p V).map
          (((fiberPseudofunctor (π₁ u p)).map
            f.op.toLoc).toFunctor.map φ) =
      ((fiberPseudofunctor p).map
          (u.map f).op.toLoc).toFunctor.map
            ((Fiber.chosen.functor u p U).map φ) ≫
        (Indexed.canonical.comparisonIso u p f Y).inv := sorry

/-- Identity coherence for the forward canonical restriction comparison. -/
theorem Indexed.canonical.comparisonIso.id.hom
    (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered]
    (U : C) (X : (π₁ u p).Fiber U) :
    (Fiber.chosen.functor u p U).map
          (((fiberPseudofunctor (π₁ u p)).mapIdOp U).inv.toNatTrans.app X) ≫
        (Indexed.canonical.comparisonIso u p (𝟙 U) X).hom =
      ((fiberPseudofunctor p).mapIdOp'
        (u.obj U) (u.map (𝟙 U)) (u.map_id U)).inv.toNatTrans.app
          ((Fiber.chosen.functor u p U).obj X) := sorry

/-- Identity coherence for the inverse canonical restriction comparison. -/
theorem Indexed.canonical.comparisonIso.id.inv
    (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered]
    (U : C) (X : (π₁ u p).Fiber U) :
    (Indexed.canonical.comparisonIso u p (𝟙 U) X).inv ≫
        (Fiber.chosen.functor u p U).map
          (((fiberPseudofunctor (π₁ u p)).mapIdOp U).hom.toNatTrans.app X) =
      ((fiberPseudofunctor p).mapIdOp'
        (u.obj U) (u.map (𝟙 U)) (u.map_id U)).hom.toNatTrans.app
          ((Fiber.chosen.functor u p U).obj X) := sorry

/-- Composition coherence for the forward canonical restriction comparison. -/
theorem Indexed.canonical.comparisonIso.comp.hom
    (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered]
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (X : (π₁ u p).Fiber U) :
    (Indexed.canonical.comparisonIso u p (g ≫ f) X).hom ≫
        ((fiberPseudofunctor p).mapCompOp'
          (u.map f) (u.map g) (u.map (g ≫ f))
          (u.map_comp g f).symm).hom.toNatTrans.app
            ((Fiber.chosen.functor u p U).obj X) =
      (Fiber.chosen.functor u p W).map
          (((fiberPseudofunctor (π₁ u p)).mapCompOp f g).hom.toNatTrans.app X) ≫
        (Indexed.canonical.comparisonIso u p g
          (((fiberPseudofunctor (π₁ u p)).map
            f.op.toLoc).toFunctor.obj X)).hom ≫
        ((fiberPseudofunctor p).map
          (u.map g).op.toLoc).toFunctor.map
            (Indexed.canonical.comparisonIso u p f X).hom := sorry

/-- Composition coherence for the inverse canonical restriction comparison. -/
theorem Indexed.canonical.comparisonIso.comp.inv
    (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered]
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (X : (π₁ u p).Fiber U) :
    ((fiberPseudofunctor p).map
          (u.map g).op.toLoc).toFunctor.map
            (Indexed.canonical.comparisonIso u p f X).inv ≫
        (Indexed.canonical.comparisonIso u p g
          (((fiberPseudofunctor (π₁ u p)).map
            f.op.toLoc).toFunctor.obj X)).inv ≫
        (Fiber.chosen.functor u p W).map
          (((fiberPseudofunctor (π₁ u p)).mapCompOp f g).inv.toNatTrans.app X) =
      ((fiberPseudofunctor p).mapCompOp'
          (u.map f) (u.map g) (u.map (g ≫ f))
          (u.map_comp g f).symm).inv.toNatTrans.app
            ((Fiber.chosen.functor u p U).obj X) ≫
        (Indexed.canonical.comparisonIso u p (g ≫ f) X).inv := sorry

end Limits.CategoricalPullback

end CategoryTheory
