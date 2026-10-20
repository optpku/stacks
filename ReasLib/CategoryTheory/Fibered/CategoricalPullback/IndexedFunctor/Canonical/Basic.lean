/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.IndexedFunctor.Comparison
public import ReasLib.CategoryTheory.Fibered.CategoricalPullback.IndexedFunctor.Chosen

/-!
# Canonical indexed fiber comparison for a categorical pullback

When both legs are presented by selected cleavages, the pullback projection
has an independently selected cleavage as well.  This module changes that
cleavage to the induced one and then applies the selected indexed comparison.
It owns the resulting canonical indexed functor, its objectwise restriction
isomorphism, cartesian characterizations, and naturality formulas.
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

/-- The pullback-fiber comparison with both source and target presented using mathlib's selected
cleavages.

The first factor changes the independently selected cleavage on `π₁ u p` to the cleavage induced
from the selected cleavage on `p`; the second factor is the coherent pullback-fiber comparison.
This is the application-facing owner matching `fiberPseudofunctor (π₁ u p)` exactly. -/
noncomputable def Indexed.canonical.functor
    (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered] :
    Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor u
      (fiberPseudofunctor (π₁ u p)) (fiberPseudofunctor p) :=
  (Cleavage.Indexed.comparison
      (Cleavage.ofIsFibered (π₁ u p))
      (Cleavage.chosen u p)).comp
    (Indexed.chosen.functor u p)

/-- Components of the canonical selected-cleavage comparison are the selected pullback-fiber
comparison functors. -/
@[simp]
theorem Indexed.canonical.functor.app
    (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered] (U : C) :
    (Indexed.canonical.functor u p).app U =
      Fiber.chosen.functor u p U := sorry

/-- Naturality of the canonical selected-cleavage comparison is the composite of
change-of-cleavage naturality and induced-pullback naturality. -/
@[simp]
theorem Indexed.canonical.functor.naturality
    (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered]
    {U V : C} (f : V ⟶ U) :
    (Indexed.canonical.functor u p).naturality f =
      Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor.compNaturality
        (Cleavage.Indexed.comparison
          (Cleavage.ofIsFibered (π₁ u p))
          (Cleavage.chosen u p))
        (Indexed.chosen.functor u p) f := sorry

/-- The objectwise restriction comparison for the canonical selected-cleavage pullback-fiber
comparison. -/
noncomputable def Indexed.canonical.comparisonIso
    (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered]
    {U V : C} (f : V ⟶ U) (X : (π₁ u p).Fiber U) :
    (Fiber.chosen.functor u p V).obj
        (((fiberPseudofunctor (π₁ u p)).map
          f.op.toLoc).toFunctor.obj X) ≅
      ((fiberPseudofunctor p).map
        (u.map f).op.toLoc).toFunctor.obj
          ((Fiber.chosen.functor u p U).obj X) :=
  ((Indexed.canonical.functor u p).naturality f).app X

/-- The cartesian composite obtained by first restricting in the independently selected
pullback cleavage and then strictifying the right component. -/
noncomputable def Indexed.canonical.comparisonIso.sourceCartesian
    (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered]
    {U V : C} (f : V ⟶ U) (X : (π₁ u p).Fiber U) :
    ((Fiber.chosen.functor u p V).obj
        (((fiberPseudofunctor (π₁ u p)).map
          f.op.toLoc).toFunctor.obj X)).1 ⟶
      X.1.snd :=
  Fiber.forward.cartesian u p
      (Cleavage.ofIsFibered p)
      (((fiberPseudofunctor (π₁ u p)).map
        f.op.toLoc).toFunctor.obj X) ≫
    ((Cleavage.ofIsFibered (π₁ u p)).cartesianHom f X).snd

/-- The cartesian composite obtained by first strictifying the right component and then
restricting it in the selected target cleavage. -/
noncomputable def Indexed.canonical.comparisonIso.targetCartesian
    (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered]
    {U V : C} (f : V ⟶ U) (X : (π₁ u p).Fiber U) :
    (((fiberPseudofunctor p).map
        (u.map f).op.toLoc).toFunctor.obj
          ((Fiber.chosen.functor u p U).obj X)).1 ⟶
      X.1.snd :=
  (Cleavage.ofIsFibered p).cartesianHom (u.map f)
      ((Fiber.chosen.functor u p U).obj X) ≫
    Fiber.forward.cartesian u p
      (Cleavage.ofIsFibered p) X

/-- The forward canonical restriction comparison is the forward naturality component of the
canonical indexed pullback-fiber comparison. -/
@[simp]
theorem Indexed.canonical.functor.naturality.hom.app
    (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered]
    {U V : C} (f : V ⟶ U) (X : (π₁ u p).Fiber U) :
    ((Indexed.canonical.functor u p).naturality f).hom.app X =
      (Indexed.canonical.comparisonIso u p f X).hom := sorry

/-- The inverse canonical restriction comparison is the inverse naturality component of the
canonical indexed pullback-fiber comparison. -/
@[simp]
theorem Indexed.canonical.functor.naturality.inv.app
    (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered]
    {U V : C} (f : V ⟶ U) (X : (π₁ u p).Fiber U) :
    ((Indexed.canonical.functor u p).naturality f).inv.app X =
      (Indexed.canonical.comparisonIso u p f X).inv := sorry

/-- The forward canonical restriction comparison is characterized by equality of the two
cartesian composites to the original right component. -/
@[reassoc]
theorem Indexed.canonical.comparisonIso.hom.fac
    (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered]
    {U V : C} (f : V ⟶ U) (X : (π₁ u p).Fiber U) :
    (Indexed.canonical.comparisonIso u p f X).hom.1 ≫
        Indexed.canonical.comparisonIso.targetCartesian u p f X =
      Indexed.canonical.comparisonIso.sourceCartesian u p f X := sorry

/-- The inverse canonical restriction comparison is characterized by equality of the two
cartesian composites to the original right component. -/
@[reassoc]
theorem Indexed.canonical.comparisonIso.inv.fac
    (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered]
    {U V : C} (f : V ⟶ U) (X : (π₁ u p).Fiber U) :
    (Indexed.canonical.comparisonIso u p f X).inv.1 ≫
        Indexed.canonical.comparisonIso.sourceCartesian u p f X =
      Indexed.canonical.comparisonIso.targetCartesian u p f X := sorry

end Limits.CategoricalPullback

end CategoryTheory
