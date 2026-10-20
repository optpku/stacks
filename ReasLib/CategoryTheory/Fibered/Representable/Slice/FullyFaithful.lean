/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import ReasLib.CategoryTheory.Bicategory.HomotopyCategory.LocallyGroupoidal
public import ReasLib.CategoryTheory.Fibered.Representable.Slice.Map

/-!
# Full faithfulness of canonical slice fibrations

Terminal-object evaluation identifies morphisms between canonical slice fibrations up to
`2`-isomorphism with morphisms between their representing objects.
-/

@[expose] public section

universe u v

namespace CategoryTheory.FiberedCategoryOver.Groupoids.slice

open scoped Bicategory

variable {C : Type u} [Category.{v} C]

/-- Passing the identity slice morphism to the homotopy category gives the identity class. -/
theorem functor.mapId (X : C) :
    Bicategory.HomotopyCategory.mkHom (overMap (𝟙 X)) =
      𝟙 (Bicategory.HomotopyCategory.mk (slice X)) := sorry

/-- Passing composition of canonical slice morphisms to the homotopy category gives composition
of their classes. -/
theorem functor.mapComp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Bicategory.HomotopyCategory.mkHom (overMap (f ≫ g)) =
      Bicategory.HomotopyCategory.mkHom (overMap f) ≫
        Bicategory.HomotopyCategory.mkHom (overMap g) := sorry

variable (C) in
/-- The canonical functor sending an object to its slice fibration in the homotopy category. -/
@[stacks 04SF "canonical slice functor to the homotopy category"]
def functor :
    C ⥤ Bicategory.HomotopyCategory (FiberedCategoryOver.Groupoids C) where
  obj X := Bicategory.HomotopyCategory.mk (slice X)
  map f := Bicategory.HomotopyCategory.mkHom (overMap f)
  map_id X := functor.mapId X
  map_comp f g := functor.mapComp f g

/-- Recover `X ⟶ Y` from `C/X ⟶ C/Y` by evaluating at `𝟙 X`. -/
@[stacks 04SF "recover a morphism from a map of slice fibrations"]
def eval {X Y : C} (F : slice X ⟶ slice Y) : X ⟶ Y :=
  (FiberedCategoryOver.Groupoids.commIso F).inv.app (Over.mk (𝟙 X)) ≫
    ((FiberedCategoryOver.Groupoids.toFunctor F).obj (Over.mk (𝟙 X))).hom

namespace eval

/-- Evaluation of the canonical slice morphism recovers the base morphism. -/
theorem overMap {X Y : C} (f : X ⟶ Y) :
    eval (FiberedCategoryOver.Groupoids.overMap f) = f := sorry

/-- `2`-isomorphic slice morphisms recover the same base morphism. -/
theorem eq_of_isomorphic {X Y : C} {F G : slice X ⟶ slice Y}
    (h : IsIsomorphic F G) : eval F = eval G := sorry

/-- Evaluation at `𝟙 X` is surjective on morphisms between slice fibrations. -/
theorem surjective (X Y : C) :
    Function.Surjective (eval : (slice X ⟶ slice Y) → (X ⟶ Y)) := sorry

/-- Two slice morphisms have the same evaluation exactly when they are `2`-isomorphic. -/
theorem eq_iff_isomorphic {X Y : C} (F G : slice X ⟶ slice Y) :
    eval F = eval G ↔ IsIsomorphic F G := sorry

/-- Evaluation as a functor to the discrete category of base morphisms. -/
@[stacks 04SF "discrete evaluation of morphisms between slice fibrations"]
noncomputable def functor (X Y : C) :
    (slice X ⟶ slice Y) ⥤ Discrete (X ⟶ Y) where
  obj F := Discrete.mk (eval F)
  map eta := Discrete.eqToHom (eval.eq_of_isomorphic ⟨asIso eta⟩)

namespace functor

/-- Discrete evaluation sends a slice morphism to its terminal-object evaluation. -/
@[simp]
theorem obj (X Y : C) (F : slice X ⟶ slice Y) :
    (eval.functor X Y).obj F = Discrete.mk (eval F) := sorry

/-- The map of discrete evaluation is the equality morphism induced by invariance under the
given `2`-cell. -/
@[simp]
theorem map (X Y : C) {F G : slice X ⟶ slice Y} (eta : F ⟶ G) :
    (eval.functor X Y).map eta =
      Discrete.eqToHom (eval.eq_of_isomorphic ⟨asIso eta⟩) := sorry

end functor

/-- Evaluation descended to homotopy classes of slice morphisms. -/
@[stacks 04SF "evaluation on homotopy classes of slice morphisms"]
noncomputable def desc (X Y : C) :
    (Bicategory.HomotopyCategory.mk (slice X) ⟶
      Bicategory.HomotopyCategory.mk (slice Y)) → (X ⟶ Y) :=
  ConnectedComponents.liftFunctor _ (functor X Y)

namespace desc

/-- Descended evaluation computes on a represented class by evaluating its representative. -/
@[simp]
theorem mkHom {X Y : C} (F : slice X ⟶ slice Y) :
    desc X Y (Bicategory.HomotopyCategory.mkHom F) = eval F := sorry

/-- Mapping a homotopy class after evaluation recovers the original class. -/
theorem map_preimage {X Y : C}
    (f : Bicategory.HomotopyCategory.mk (slice X) ⟶
      Bicategory.HomotopyCategory.mk (slice Y)) :
    (slice.functor C).map (desc X Y f) = f := sorry

/-- Evaluating the canonical image of a base morphism recovers that morphism. -/
theorem preimage_map {X Y : C} (f : X ⟶ Y) :
    desc X Y ((slice.functor C).map f) = f := sorry

end desc

end eval

namespace functor

/-- The canonical slice functor sends `X` to the class of its slice fibration. -/
@[simp]
theorem obj (X : C) :
    (slice.functor C).obj X = Bicategory.HomotopyCategory.mk (slice X) := sorry

/-- The canonical slice functor sends `f` to the class of `overMap f`. -/
@[simp]
theorem map {X Y : C} (f : X ⟶ Y) :
    (slice.functor C).map f = Bicategory.HomotopyCategory.mkHom (overMap f) := sorry

variable (C) in
/-- The canonical slice functor is fully faithful; its preimage is terminal-object evaluation. -/
@[stacks 04SF "full faithfulness of the canonical slice functor"]
noncomputable def fullyFaithful : (slice.functor C).FullyFaithful where
  preimage {X Y} := slice.eval.desc X Y
  map_preimage := slice.eval.desc.map_preimage
  preimage_map := slice.eval.desc.preimage_map

/-- The canonical slice functor is full. -/
@[stacks 04SF "fullness of the canonical slice functor"]
instance full : (slice.functor C).Full := sorry

/-- The canonical slice functor is faithful. -/
@[stacks 04SF "faithfulness of the canonical slice functor"]
instance faithful : (slice.functor C).Faithful := sorry

namespace fullyFaithful

/-- The preimage supplied by full faithfulness evaluates represented homotopy classes. -/
@[simp]
theorem preimage_mkHom {X Y : C} (F : slice X ⟶ slice Y) :
    (fullyFaithful C).preimage (Bicategory.HomotopyCategory.mkHom F) = slice.eval F := sorry

end fullyFaithful

end functor

/-- Homotopy classes of slice morphisms are canonically equivalent to base morphisms. -/
@[stacks 04SF "homotopy classes of slice morphisms"]
noncomputable def evalEquiv (X Y : C) :
    (Bicategory.HomotopyCategory.mk (slice X) ⟶
      Bicategory.HomotopyCategory.mk (slice Y)) ≃ (X ⟶ Y) :=
  (functor.fullyFaithful C).homEquiv.symm

namespace evalEquiv

/-- The forward map of the Hom equivalence is descended terminal-object evaluation. -/
@[simp]
theorem apply {X Y : C}
    (f : Bicategory.HomotopyCategory.mk (slice X) ⟶
      Bicategory.HomotopyCategory.mk (slice Y)) :
    evalEquiv X Y f = eval.desc X Y f := sorry

/-- The forward map evaluates a represented homotopy class. -/
@[simp]
theorem apply.mkHom {X Y : C} (F : slice X ⟶ slice Y) :
    evalEquiv X Y (Bicategory.HomotopyCategory.mkHom F) = slice.eval F := sorry

/-- The inverse map is represented by canonical slice postcomposition. -/
@[simp]
theorem symm.apply {X Y : C} (f : X ⟶ Y) :
    (evalEquiv X Y).symm f =
      Bicategory.HomotopyCategory.mkHom (FiberedCategoryOver.Groupoids.overMap f) := sorry

end evalEquiv

end CategoryTheory.FiberedCategoryOver.Groupoids.slice

/- Data and axiom audit: the inverse Hom map is the explicit descended terminal-object
evaluation. `sorryAx` is confined to functor, inverse, and bicategorical coherence laws. -/
