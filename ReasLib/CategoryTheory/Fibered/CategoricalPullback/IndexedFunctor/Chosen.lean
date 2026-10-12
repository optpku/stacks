/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.CategoricalPullback.IndexedFunctor.Explicit
public import ReasLib.CategoryTheory.Fibered.CategoricalPullback.Fiber.Chosen
public import ReasLib.CategoryTheory.Fibered.CategoricalPullback.Reindex.Chosen
public import ReasLib.CategoryTheory.Fibered.ChosenCleavage.Pseudofunctor

/-!
# Chosen indexed fiber comparison for a categorical pullback

This is the application-facing specialization of the explicit indexed fiber
comparison to `Functor.Cleavage.ofIsFibered`.  The explicit module remains
the owner of the concrete construction and its choice-free coherence data.
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

namespace Indexed.chosen

/-- The indexed pullback-fiber comparison specialized to mathlib's selected cleavage on a fibred
right leg. -/
noncomputable def functor
    (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered] :
    Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor u
      (Cleavage.chosen u p).toPseudofunctor
      (fiberPseudofunctor p) :=
  Indexed.explicit.functor u p (Cleavage.ofIsFibered p)

/-- The selected indexed comparison has the selected pullback-fiber functor as each component. -/
@[simp]
theorem functor.app
    (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered] (U : C) :
    (functor u p).app U = Fiber.chosen.functor u p U := sorry

/-- The naturality isomorphism of the selected indexed comparison is the selected reindexing
comparison. -/
@[simp]
theorem functor.naturality
    (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered]
    {U V : C} (f : V ⟶ U) :
    (functor u p).naturality f = Reindex.chosen.comparisonNatIso u p f := sorry

/-- The forward component of selected indexed-comparison naturality. -/
@[simp]
theorem functor.naturality.hom.app
    (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered]
    {U V : C} (f : V ⟶ U) (X : (π₁ u p).Fiber U) :
    ((functor u p).naturality f).hom.app X =
      (Reindex.chosen.comparisonNatIso u p f).hom.app X := sorry

/-- The inverse component of selected indexed-comparison naturality. -/
@[simp]
theorem functor.naturality.inv.app
    (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered]
    {U V : C} (f : V ⟶ U) (X : (π₁ u p).Fiber U) :
    ((functor u p).naturality f).inv.app X =
      (Reindex.chosen.comparisonNatIso u p f).inv.app X := sorry

/-- Restricted-morphism transport through the selected indexed pullback-fiber comparison. -/
@[simp]
theorem functor.mapHom
    (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered]
    {U₁ U₂ V : C} (f₁ : V ⟶ U₁) (f₂ : V ⟶ U₂)
    {X : (π₁ u p).Fiber U₁} {Y : (π₁ u p).Fiber U₂}
    (φ :
      (((Cleavage.chosen u p).toPseudofunctor.map
        f₁.op.toLoc).toFunctor.obj X) ⟶
      (((Cleavage.chosen u p).toPseudofunctor.map
        f₂.op.toLoc).toFunctor.obj Y)) :
    (functor u p).mapHom f₁ f₂ φ =
      (Reindex.chosen.comparisonNatIso u p f₁).inv.app X ≫
        (Fiber.chosen.functor u p V).map φ ≫
        (Reindex.chosen.comparisonNatIso u p f₂).hom.app Y := sorry

/-- Total-category readout of selected indexed restricted-morphism transport. -/
theorem functor.mapHom.toTotal
    (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered]
    {U₁ U₂ V : C} (f₁ : V ⟶ U₁) (f₂ : V ⟶ U₂)
    {X : (π₁ u p).Fiber U₁} {Y : (π₁ u p).Fiber U₂}
    (φ :
      (((Cleavage.chosen u p).toPseudofunctor.map
        f₁.op.toLoc).toFunctor.obj X) ⟶
      (((Cleavage.chosen u p).toPseudofunctor.map
        f₂.op.toLoc).toFunctor.obj Y)) :
    ((functor u p).mapHom f₁ f₂ φ).1 =
      ((Reindex.chosen.comparisonNatIso u p f₁).inv.app X).1 ≫
        ((Fiber.chosen.functor u p V).map φ).1 ≫
        ((Reindex.chosen.comparisonNatIso u p f₂).hom.app Y).1 := sorry

/-- The selected indexed pullback-fiber comparison is an equivalence on every fiber. -/
instance functor.fiberwiseEquivalence
    (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered] :
    (functor u p).FiberwiseEquivalence := sorry

end Indexed.chosen

end Limits.CategoricalPullback

end CategoryTheory
