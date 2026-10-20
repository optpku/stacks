/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Inertia.Functoriality.Computations.Action.Objects
public import ReasLib.CategoryTheory.Inertia.Functoriality.Comparison.Identity
public import ReasLib.CategoryTheory.Inertia.Functoriality.Comparison.Composition

/-!
# Comparison computations for the ordinary inertia pseudofunctor

This leaf exposes both directions of the packaged identity and composition comparisons, including
their Cat-wrapper projections and underlying arrows.
-/

@[expose] public section

open CategoryTheory
open Bicategory
open scoped Bicategory

universe u v

namespace CategoryTheory
namespace Inertia

/-- The identity comparison of the inertia pseudofunctor is the explicit componentwise identity
comparison. -/
@[simp]
theorem pseudofunctor.mapId (C : Cat.{v, u}) :
    pseudofunctor.mapId C =
      Cat.Hom.isoMk (mapIdIso (C := C)) := sorry

/-- After forgetting the Cat wrapper, the identity comparison is `mapIdIso`. -/
@[simp]
theorem pseudofunctor.mapId.toNatIso (C : Cat.{v, u}) :
    Cat.Hom.toNatIso ((pseudofunctor).mapId C) =
      mapIdIso (C := C) := sorry

/-- The forward component of the pseudofunctor identity comparison is the explicit objectwise
inertia comparison. -/
@[simp]
theorem pseudofunctor.mapId.hom.app (C : Cat.{v, u}) (X : Inertia C) :
    (Cat.Hom.toNatIso ((pseudofunctor).mapId C)).hom.app X =
      (mapIdIso.app X).hom := sorry

/-- The inverse component of the pseudofunctor identity comparison is the inverse explicit
objectwise inertia comparison. -/
@[simp]
theorem pseudofunctor.mapId.inv.app (C : Cat.{v, u}) (X : Inertia C) :
    (Cat.Hom.toNatIso ((pseudofunctor).mapId C)).inv.app X =
      (mapIdIso.app X).inv := sorry

/-- The ambient arrow underlying a forward identity-comparison component is an identity. -/
@[simp]
theorem pseudofunctor.mapId.hom.app.underlying (C : Cat.{v, u}) (X : Inertia C) :
    Inertia.hom ((Cat.Hom.toNatIso ((pseudofunctor).mapId C)).hom.app X) =
      𝟙 X.obj := sorry

/-- The ambient arrow underlying an inverse identity-comparison component is an identity. -/
@[simp]
theorem pseudofunctor.mapId.inv.app.underlying (C : Cat.{v, u}) (X : Inertia C) :
    Inertia.hom ((Cat.Hom.toNatIso ((pseudofunctor).mapId C)).inv.app X) =
      𝟙 X.obj := sorry

/-- The composition comparison of the inertia pseudofunctor is the explicit componentwise
composition comparison. -/
@[simp]
theorem pseudofunctor.mapComp
    {C D E : Cat.{v, u}} (F : C ⟶ D) (G : D ⟶ E) :
    pseudofunctor.mapComp F G =
      Cat.Hom.isoMk (mapCompIso F.toFunctor G.toFunctor) := sorry

/-- After forgetting the Cat wrapper, the composition comparison is `mapCompIso`. -/
@[simp]
theorem pseudofunctor.mapComp.toNatIso
    {C D E : Cat.{v, u}} (F : C ⟶ D) (G : D ⟶ E) :
    Cat.Hom.toNatIso ((pseudofunctor).mapComp F G) =
      mapCompIso F.toFunctor G.toFunctor := sorry

/-- The forward component of the pseudofunctor composition comparison is the explicit objectwise
inertia comparison. -/
@[simp]
theorem pseudofunctor.mapComp.hom.app
    {C D E : Cat.{v, u}} (F : C ⟶ D) (G : D ⟶ E) (X : Inertia C) :
    (Cat.Hom.toNatIso ((pseudofunctor).mapComp F G)).hom.app X =
      (mapCompIso.app F.toFunctor G.toFunctor X).hom := sorry

/-- The inverse component of the pseudofunctor composition comparison is the inverse explicit
objectwise inertia comparison. -/
@[simp]
theorem pseudofunctor.mapComp.inv.app
    {C D E : Cat.{v, u}} (F : C ⟶ D) (G : D ⟶ E) (X : Inertia C) :
    (Cat.Hom.toNatIso ((pseudofunctor).mapComp F G)).inv.app X =
      (mapCompIso.app F.toFunctor G.toFunctor X).inv := sorry

/-- The ambient arrow underlying a forward composition-comparison component is an identity. -/
@[simp]
theorem pseudofunctor.mapComp.hom.app.underlying
    {C D E : Cat.{v, u}} (F : C ⟶ D) (G : D ⟶ E) (X : Inertia C) :
    Inertia.hom ((Cat.Hom.toNatIso ((pseudofunctor).mapComp F G)).hom.app X) =
      𝟙 (((Inertia.map F.toFunctor ⋙ Inertia.map G.toFunctor).obj X).obj) := sorry

/-- The ambient arrow underlying an inverse composition-comparison component is an identity. -/
@[simp]
theorem pseudofunctor.mapComp.inv.app.underlying
    {C D E : Cat.{v, u}} (F : C ⟶ D) (G : D ⟶ E) (X : Inertia C) :
    Inertia.hom ((Cat.Hom.toNatIso ((pseudofunctor).mapComp F G)).inv.app X) =
      𝟙 (((Inertia.map F.toFunctor ⋙ Inertia.map G.toFunctor).obj X).obj) := sorry

end Inertia
end CategoryTheory
