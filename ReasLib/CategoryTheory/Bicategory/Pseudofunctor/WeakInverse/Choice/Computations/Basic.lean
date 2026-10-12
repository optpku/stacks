/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.WeakInverse.Choice.Construction

/-!
# Basic computations for a chosen pseudoinverse

This file exposes the object and local action, comparison isomorphisms, and
local-image naturality of the chosen pseudoinverse.
-/

@[expose] public section

universe wB vB uB wC vC uC

namespace CategoryTheory.Pseudofunctor

open Bicategory
open scoped Bicategory

variable {B : Type uB} [Bicategory.{wB, vB} B]
variable {C : Type uC} [Bicategory.{wC, vC} C]
variable (F : B ⥤ᵖ C) [F.IsBiequivalence]

/-- The chosen pseudoinverse sends an object to the selected object preimage. -/
@[simp]
theorem chosenInverse.obj (X : C) :
    F.chosenInverse.obj X = F.objPreimage X := sorry

/-- The local action functor of the chosen pseudoinverse is the selected
inverse after transport across the chosen object equivalences. -/
@[simp]
theorem chosenInverse.mapFunctor (X Y : C) :
    F.chosenInverse.mapFunctor X Y =
      ChosenInverse.homFunctor F X Y := sorry

/-- The action of the chosen pseudoinverse on `1`-morphisms is the selected
local inverse after transport across the object equivalences. -/
@[simp]
theorem chosenInverse.map {X Y : C} (f : X ⟶ Y) :
    F.chosenInverse.map f = (ChosenInverse.homFunctor F X Y).obj f := sorry

/-- The action of the chosen pseudoinverse on `2`-morphisms is the map of its
selected local inverse functor. -/
@[simp]
theorem chosenInverse.map₂ {X Y : C} {f g : X ⟶ Y} (α : f ⟶ g) :
    F.chosenInverse.map₂ α = (ChosenInverse.homFunctor F X Y).map α := sorry

/-- The identity comparison of the chosen pseudoinverse is the explicit
lifted identity isomorphism. -/
@[simp]
theorem chosenInverse.mapId (X : C) :
    F.chosenInverse.mapId X = ChosenInverse.mapIdIso F X := sorry

/-- The composition comparison of the chosen pseudoinverse is the explicit
lifted composition isomorphism. -/
@[simp]
theorem chosenInverse.mapComp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    F.chosenInverse.mapComp f g = ChosenInverse.mapCompIso F f g := sorry

namespace ChosenInverse

/-- Transport across the chosen object equivalences acts on a morphism by
precomposition with the source equivalence and postcomposition with the
inverse target equivalence. -/
@[simp]
theorem mapImage.transport.obj (X Y : C) (f : X ⟶ Y) :
    (mapImage.transport F X Y).obj f =
      ((objPreimage.equivalence F X).hom ≫ f) ≫
        (objPreimage.equivalence F Y).inv := sorry

/-- Transport across the chosen object equivalences acts on a `2`-morphism
by whiskering with the selected source and target equivalences. -/
@[simp]
theorem mapImage.transport.map {X Y : C} {f g : X ⟶ Y} (α : f ⟶ g) :
    (mapImage.transport F X Y).map α =
      ((objPreimage.equivalence F X).hom ◁ α) ▷
        (objPreimage.equivalence F Y).inv := sorry

/-- The component of the bundled local-image comparison is the pointwise
local-image isomorphism. -/
@[simp]
theorem mapImage.natIso.app {X Y : C} (f : X ⟶ Y) :
    (mapImage.natIso F X Y).app f = mapImage.iso F f := sorry

/-- The forward local-image comparison is natural in `2`-morphisms. -/
theorem mapImage.iso.hom.naturality {X Y : C} {f g : X ⟶ Y}
    (α : f ⟶ g) :
    F.map₂ (F.chosenInverse.map₂ α) ≫ (mapImage.iso F g).hom =
      (mapImage.iso F f).hom ≫
        (((objPreimage.equivalence F X).hom ◁ α) ▷
          (objPreimage.equivalence F Y).inv) := sorry

/-- The inverse local-image comparison is natural in `2`-morphisms. -/
theorem mapImage.iso.inv.naturality {X Y : C} {f g : X ⟶ Y}
    (α : f ⟶ g) :
    (((objPreimage.equivalence F X).hom ◁ α) ▷
        (objPreimage.equivalence F Y).inv) ≫ (mapImage.iso F g).inv =
      (mapImage.iso F f).inv ≫
        F.map₂ (F.chosenInverse.map₂ α) := sorry

end ChosenInverse

end CategoryTheory.Pseudofunctor
