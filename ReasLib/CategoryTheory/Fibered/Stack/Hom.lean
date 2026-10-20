/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.Over
public import ReasLib.CategoryTheory.Bicategory.InducedBicategory.LocalProperties
public import ReasLib.CategoryTheory.Fibered.CategoryOver.HomSheaf
import Mathlib.Tactic.CrossRefAttribute

/-!
# Hom categories of bundled stacks

The bicategory `StackOver J` is a full induced subbicategory of the bicategory of fibred
categories over the base.  This file exposes the resulting equivalence between each stack Hom
category and its ambient fibred-category Hom category.

## Main declarations

* `CategoryTheory.StackOver.Hom.ambientEquivalence` — the canonical local equivalence.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory

open Bicategory
open scoped Bicategory

namespace StackOver.Hom

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable (X Y : StackOver.{u, v, w, vS} J)

/-- The canonical equivalence from the ambient fibred-category Hom category to the Hom category
of stacks. It specializes the data-preserving equivalence for any induced bicategory. -/
@[stacks 04WQ "ambient-to-stack Hom equivalence"]
abbrev ambientEquivalence :
    (X.toFiberedCategoryOver ⟶ Y.toFiberedCategoryOver) ≌ (X ⟶ Y) :=
  Bicategory.InducedBicategory.homEquivalence X Y

end StackOver.Hom

namespace StackOver.Hom

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {X Y Z : StackOver.{u, v, w, vS} J}

/-- The canonical map of Hom-sheaves induced by a morphism of bundled stacks. The topology is
inferred from the stack owners, so consumers need only supply the morphism and fiber objects. -/
@[stacks 04WQ "canonical bundled Hom-sheaf map"]
noncomputable abbrev sheafHomMap
    (F : X ⟶ Y) {U : C} (x y : X.p.Fiber U) :
    (Functor.fiberPseudofunctor X.p).sheafHom J x y ⟶
      (Functor.fiberPseudofunctor Y.p).sheafHom J
        ((fiberFunctor F U).obj x) ((fiberFunctor F U).obj y) :=
  FiberedCategoryOver.Hom.sheafHomMap (toMor F) J x y

namespace SheafMap

/-- Forgetting the stack Hom-sheaf map recovers the canonical Hom-presheaf map. -/
@[simp, stacks 04WQ "bundled Hom-sheaf map underlying presheaf readout"]
theorem hom (F : X ⟶ Y) {U : C} (x y : X.p.Fiber U) :
    (sheafHomMap F x y).hom =
      FiberedCategoryOver.Hom.presheafHomMap (toMor F) x y := sorry

/-- The identity stack morphism induces the identity map of every Hom-sheaf. -/
@[simp, stacks 04WQ "identity law for bundled Hom-sheaf maps"]
theorem id (X : StackOver.{u, v, w, vS} J) {U : C} (x y : X.p.Fiber U) :
    sheafHomMap (𝟙 X) x y =
      𝟙 ((Functor.fiberPseudofunctor X.p).sheafHom J x y) := sorry

/-- Canonical Hom-sheaf maps of stack morphisms preserve composition. -/
@[stacks 04WQ "composition law for bundled Hom-sheaf maps"]
theorem comp (F : X ⟶ Y) (G : Y ⟶ Z) {U : C} (x y : X.p.Fiber U) :
    sheafHomMap (F ≫ G) x y =
      sheafHomMap F x y ≫
        sheafHomMap G ((fiberFunctor F U).obj x) ((fiberFunctor F U).obj y) := sorry

/-- A stack Hom-sheaf map is an isomorphism exactly when its underlying Hom-presheaf map is. -/
@[stacks 04WQ "bundled Hom-sheaf map isomorphism readout"]
theorem isIso_iff (F : X ⟶ Y) {U : C} (x y : X.p.Fiber U) :
    IsIso (sheafHomMap F x y) ↔
      IsIso (FiberedCategoryOver.Hom.presheafHomMap (toMor F) x y) := sorry

/-- A morphism of bundled stacks is fully faithful exactly when all of its canonical
Hom-sheaf maps are isomorphisms. -/
@[stacks 04WQ "bundled full faithfulness via Hom-sheaves"]
theorem fullyFaithful_iff_isIso (F : X ⟶ Y) :
    Nonempty (StackOver.Hom.toBasedFunctor F).FullyFaithful ↔
      ∀ {U : C} (x y : X.p.Fiber U), IsIso (sheafHomMap F x y) := sorry

end SheafMap

end StackOver.Hom

namespace StackOver.Hom.PresheafMap

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {X Y : StackOver.{u, v, w, vS} J}

/-- A morphism of bundled stacks is fully faithful exactly when all canonical fiberwise
Hom-presheaf maps of its underlying fibred-category morphism are isomorphisms. -/
@[stacks 04WQ "bundled full faithfulness via Hom-presheaves"]
theorem fullyFaithful_iff_isIso (F : X ⟶ Y) :
    Nonempty (StackOver.Hom.toBasedFunctor F).FullyFaithful ↔
      ∀ {U : C} (x y : X.p.Fiber U),
        IsIso (FiberedCategoryOver.Hom.presheafHomMap
          (StackOver.Hom.toMor F) x y) := sorry

end StackOver.Hom.PresheafMap

end CategoryTheory
