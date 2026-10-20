/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Map.Absolute.Computations
public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.Comparison.Composition
import Mathlib.Tactic.CrossRefAttribute

/-!
# Composition comparison for cartesian absolute inertia

This leaf owns the fibred composition comparison and its based, component, and underlying-arrow
readouts. Identity comparison is provided by the sibling `Identity` leaf.
-/

@[expose] public section

universe u v vS w

namespace CategoryTheory

open BasedCategory BasedFunctor
open scoped Bicategory

namespace FiberedCategoryOver.Inertia

variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.{u, v, w, vS} C}

/-- The explicit based composition comparison lifts canonically to an isomorphism of fibred
inertia morphisms. -/
def mapCompIso
    {Z : FiberedCategoryOver.{u, v, w, vS} C}
    (F : X ⟶ Y) (G : Y ⟶ Z) :
    map (F ≫ G) ≅ map F ≫ map G :=
  FiberedCategoryOver.BasedFunctorIso.lift
    (BasedCategory.Inertia.mapCompIso
      (FiberedCategoryOver.toBasedFunctor F)
      (FiberedCategoryOver.toBasedFunctor G))

namespace mapCompIso

/-- Forgetting the forward fibred composition-comparison cell recovers the explicit based comparison. -/
@[simp]
theorem hom.toBasedNatTrans
    {Z : FiberedCategoryOver.{u, v, w, vS} C}
    (F : X ⟶ Y) (G : Y ⟶ Z) :
    FiberedCategoryOver.toBasedNatTrans (mapCompIso F G).hom =
      (BasedCategory.Inertia.mapCompIso
        (FiberedCategoryOver.toBasedFunctor F)
        (FiberedCategoryOver.toBasedFunctor G)).hom := sorry

/-- Forgetting the inverse fibred composition-comparison cell recovers the explicit based comparison. -/
@[simp]
theorem inv.toBasedNatTrans
    {Z : FiberedCategoryOver.{u, v, w, vS} C}
    (F : X ⟶ Y) (G : Y ⟶ Z) :
    FiberedCategoryOver.toBasedNatTrans (mapCompIso F G).inv =
      (BasedCategory.Inertia.mapCompIso
        (FiberedCategoryOver.toBasedFunctor F)
        (FiberedCategoryOver.toBasedFunctor G)).inv := sorry

/-- The forward component of the fibred composition comparison is the explicit based component. -/
@[simp]
theorem hom.app
    {Z : FiberedCategoryOver.{u, v, w, vS} C}
    (F : X ⟶ Y) (G : Y ⟶ Z)
    (A : (FiberedCategoryOver.inertia X).total) :
    (FiberedCategoryOver.toNatTrans (mapCompIso F G).hom).app A =
      (BasedCategory.Inertia.mapCompIso.app
        (FiberedCategoryOver.toBasedFunctor F)
        (FiberedCategoryOver.toBasedFunctor G) A).hom := sorry

/-- The inverse component of the fibred composition comparison is the explicit based component. -/
@[simp]
theorem inv.app
    {Z : FiberedCategoryOver.{u, v, w, vS} C}
    (F : X ⟶ Y) (G : Y ⟶ Z)
    (A : (FiberedCategoryOver.inertia X).total) :
    (FiberedCategoryOver.toNatTrans (mapCompIso F G).inv).app A =
      (BasedCategory.Inertia.mapCompIso.app
        (FiberedCategoryOver.toBasedFunctor F)
        (FiberedCategoryOver.toBasedFunctor G) A).inv := sorry

/-- Every forward fibred composition-comparison component lies over the identity of its source
base object. -/
theorem hom.app.isHomLift
    {Z : FiberedCategoryOver.{u, v, w, vS} C}
    (F : X ⟶ Y) (G : Y ⟶ Z)
    (A : (FiberedCategoryOver.inertia X).total) :
    (FiberedCategoryOver.inertia Z).p.IsHomLift
      (𝟙 ((FiberedCategoryOver.inertia X).p.obj A))
      ((FiberedCategoryOver.toNatTrans (mapCompIso F G).hom).app A) := sorry

/-- Every inverse fibred composition-comparison component lies over the identity of its source
base object. -/
theorem inv.app.isHomLift
    {Z : FiberedCategoryOver.{u, v, w, vS} C}
    (F : X ⟶ Y) (G : Y ⟶ Z)
    (A : (FiberedCategoryOver.inertia X).total) :
    (FiberedCategoryOver.inertia Z).p.IsHomLift
      (𝟙 ((FiberedCategoryOver.inertia X).p.obj A))
      ((FiberedCategoryOver.toNatTrans (mapCompIso F G).inv).app A) := sorry

/-- The total-category arrow underlying a forward composition-comparison component is an
identity. -/
@[simp]
theorem hom.app.underlying
    {Z : FiberedCategoryOver.{u, v, w, vS} C}
    (F : X ⟶ Y) (G : Y ⟶ Z)
    (A : (FiberedCategoryOver.inertia X).total) :
    RelativeInertia.hom
        ((FiberedCategoryOver.toNatTrans (mapCompIso F G).hom).app A) =
      𝟙 (((BasedCategory.Inertia.map
        (FiberedCategoryOver.toBasedFunctor F) ⋙
          BasedCategory.Inertia.map
            (FiberedCategoryOver.toBasedFunctor G)).obj A).obj) := sorry

/-- The total-category arrow underlying an inverse composition-comparison component is an
identity. -/
@[simp]
theorem inv.app.underlying
    {Z : FiberedCategoryOver.{u, v, w, vS} C}
    (F : X ⟶ Y) (G : Y ⟶ Z)
    (A : (FiberedCategoryOver.inertia X).total) :
    RelativeInertia.hom
        ((FiberedCategoryOver.toNatTrans (mapCompIso F G).inv).app A) =
      𝟙 (((BasedCategory.Inertia.map
        (FiberedCategoryOver.toBasedFunctor F) ⋙
          BasedCategory.Inertia.map
            (FiberedCategoryOver.toBasedFunctor G)).obj A).obj) := sorry

end mapCompIso

end FiberedCategoryOver.Inertia

end CategoryTheory
