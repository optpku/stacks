/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Inertia.Functoriality.Strict.Action
public import ReasLib.CategoryTheory.Inertia.Functoriality.Comparison.Identity
public import ReasLib.CategoryTheory.Inertia.Functoriality.Comparison.Composition

/-!
# Strict inertia comparison computations

This leaf exposes strict identity and composition laws and the componentwise comparison bridges.
-/

@[expose] public section

open CategoryTheory
open Bicategory
open scoped Bicategory

universe u v

namespace CategoryTheory
namespace Inertia

/-- The strict inertia pseudofunctor preserves identity `1`-morphisms on the nose. -/
@[simp]
theorem strictPseudofunctor.map_id (C : Cat.{v, u}) :
    (strictPseudofunctor).map (𝟙 C) =
      𝟙 ((strictPseudofunctor).obj C) := sorry

/-- The strict inertia pseudofunctor preserves horizontal composition on the nose. -/
@[simp]
theorem strictPseudofunctor.map_comp
    {C D E : Cat.{v, u}} (F : C ⟶ D) (G : D ⟶ E) :
    (strictPseudofunctor).map (F ≫ G) =
      (strictPseudofunctor).map F ≫ (strictPseudofunctor).map G := sorry

/-- The identity comparison of the strict inertia pseudofunctor is the explicit componentwise
identity comparison. -/
@[simp]
theorem strictPseudofunctor.mapId (C : Cat.{v, u}) :
    (strictPseudofunctor).mapId C =
      Cat.Hom.isoMk (mapIdIso (C := C)) := sorry

/-- The forward component of the strict identity comparison is the explicit inertia component. -/
@[simp]
theorem strictPseudofunctor.mapId.hom.app (C : Cat.{v, u}) (X : Inertia C) :
    (Cat.Hom.toNatIso ((strictPseudofunctor).mapId C)).hom.app X =
      (mapIdIso.app X).hom := sorry

/-- The inverse component of the strict identity comparison is the explicit inertia component. -/
@[simp]
theorem strictPseudofunctor.mapId.inv.app (C : Cat.{v, u}) (X : Inertia C) :
    (Cat.Hom.toNatIso ((strictPseudofunctor).mapId C)).inv.app X =
      (mapIdIso.app X).inv := sorry

/-- The forward identity-comparison component has identity underlying arrow. -/
@[simp]
theorem strictPseudofunctor.mapId.hom.app.underlying (C : Cat.{v, u}) (X : Inertia C) :
    Inertia.hom ((Cat.Hom.toNatIso ((strictPseudofunctor).mapId C)).hom.app X) =
      𝟙 X.obj := sorry

/-- The inverse identity-comparison component has identity underlying arrow. -/
@[simp]
theorem strictPseudofunctor.mapId.inv.app.underlying (C : Cat.{v, u}) (X : Inertia C) :
    Inertia.hom ((Cat.Hom.toNatIso ((strictPseudofunctor).mapId C)).inv.app X) =
      𝟙 X.obj := sorry

/-- The composition comparison of the strict inertia pseudofunctor is the explicit componentwise
composition comparison. -/
@[simp]
theorem strictPseudofunctor.mapComp
    {C D E : Cat.{v, u}} (F : C ⟶ D) (G : D ⟶ E) :
    (strictPseudofunctor).mapComp F G =
      Cat.Hom.isoMk (mapCompIso F.toFunctor G.toFunctor) := sorry

/-- The forward component of the strict composition comparison is the explicit inertia component. -/
@[simp]
theorem strictPseudofunctor.mapComp.hom.app
    {C D E : Cat.{v, u}} (F : C ⟶ D) (G : D ⟶ E) (X : Inertia C) :
    (Cat.Hom.toNatIso ((strictPseudofunctor).mapComp F G)).hom.app X =
      (mapCompIso.app F.toFunctor G.toFunctor X).hom := sorry

/-- The inverse component of the strict composition comparison is the explicit inertia component. -/
@[simp]
theorem strictPseudofunctor.mapComp.inv.app
    {C D E : Cat.{v, u}} (F : C ⟶ D) (G : D ⟶ E) (X : Inertia C) :
    (Cat.Hom.toNatIso ((strictPseudofunctor).mapComp F G)).inv.app X =
      (mapCompIso.app F.toFunctor G.toFunctor X).inv := sorry

/-- The forward composition-comparison component has identity underlying arrow. -/
@[simp]
theorem strictPseudofunctor.mapComp.hom.app.underlying
    {C D E : Cat.{v, u}} (F : C ⟶ D) (G : D ⟶ E) (X : Inertia C) :
    Inertia.hom ((Cat.Hom.toNatIso ((strictPseudofunctor).mapComp F G)).hom.app X) =
      𝟙 (((Inertia.map F.toFunctor ⋙ Inertia.map G.toFunctor).obj X).obj) := sorry

/-- The inverse composition-comparison component has identity underlying arrow. -/
@[simp]
theorem strictPseudofunctor.mapComp.inv.app.underlying
    {C D E : Cat.{v, u}} (F : C ⟶ D) (G : D ⟶ E) (X : Inertia C) :
    Inertia.hom ((Cat.Hom.toNatIso ((strictPseudofunctor).mapComp F G)).inv.app X) =
      𝟙 (((Inertia.map F.toFunctor ⋙ Inertia.map G.toFunctor).obj X).obj) := sorry

end Inertia
end CategoryTheory
