/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.NatTrans
public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Pseudofunctor.Construction

/-!
# Action computations for strict fibred inertia

This leaf identifies the object, local-hom, `1`-morphism, and `2`-morphism
fields of strict fibred inertia with their reusable data owners.  It also
exposes the on-the-nose identity and composition laws expected from a strict
pseudofunctor.
-/

@[expose] public section

universe u v vS w

namespace CategoryTheory

open BasedCategory BasedFunctor
open scoped Bicategory

namespace FiberedCategoryOver.Inertia

variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.{u, v, w, vS} C}

/-- The ordinary pseudofunctor underlying strict fibred inertia is its
canonical view. -/
@[simp]
theorem strictPseudofunctor.toPseudofunctor :
    (strictPseudofunctor C).toPseudofunctor = pseudofunctor C := sorry

/-- Strict fibred inertia sends a fibred category to its inertia. -/
@[simp]
theorem strictPseudofunctor.obj
    (X : FiberedCategoryOver.{u, v, w, vS} C) :
    (strictPseudofunctor C).obj X = FiberedCategoryOver.inertia X := sorry

/-- The local action of strict fibred inertia is the canonical inertia map
functor. -/
@[simp]
theorem strictPseudofunctor.mapFunctor
    (X Y : FiberedCategoryOver.{u, v, w, vS} C) :
    (strictPseudofunctor C).mapFunctor X Y = mapFunctor X Y := sorry

/-- Evaluating the strict local hom functor on a `1`-cell gives the
canonical cartesian inertia map. -/
@[simp]
theorem strictPseudofunctor.mapFunctor.obj (F : X ⟶ Y) :
    ((strictPseudofunctor C).mapFunctor X Y).obj F =
      FiberedCategoryOver.Inertia.map F := sorry

/-- Evaluating the strict local hom functor on a `2`-cell gives the
canonical cartesian inertia action. -/
@[simp]
theorem strictPseudofunctor.mapFunctor.map
    {F G : X ⟶ Y} (τ : F ⟶ G) :
    ((strictPseudofunctor C).mapFunctor X Y).map τ =
      FiberedCategoryOver.Inertia.map₂ τ := sorry

/-- Evaluating the strict local hom functor on a `1`-cell gives the neutral
inertia map at the based level. -/
@[simp]
theorem strictPseudofunctor.mapFunctor.obj.toBasedFunctor (F : X ⟶ Y) :
    FiberedCategoryOver.toBasedFunctor
        ((strictPseudofunctor C).mapFunctor X Y |>.obj F) =
      BasedCategory.Inertia.map
        (FiberedCategoryOver.toBasedFunctor F) := sorry

/-- The semantic based-natural-transformation projection of the strict local
action is the neutral inertia `2`-cell. -/
@[simp]
theorem strictPseudofunctor.mapFunctor.map.toBasedNatTrans
    {F G : X ⟶ Y} (τ : F ⟶ G) :
    FiberedCategoryOver.toBasedNatTrans
        ((strictPseudofunctor C).mapFunctor X Y |>.map τ) =
      BasedCategory.Inertia.map₂ (FiberedCategoryOver.toBasedNatTrans τ) := sorry

/-- The strict `1`-cell action is the canonical bundled inertia map. -/
@[simp]
theorem strictPseudofunctor.map (F : X ⟶ Y) :
    (strictPseudofunctor C).map F = map F := sorry

/-- The based functor underlying the strict fibred-inertia action is the
neutral inertia map. -/
@[simp]
theorem strictPseudofunctor.map.toBasedFunctor (F : X ⟶ Y) :
    FiberedCategoryOver.toBasedFunctor ((strictPseudofunctor C).map F) =
      BasedCategory.Inertia.map
        (FiberedCategoryOver.toBasedFunctor F) := sorry

/-- Strict fibred inertia preserves identity `1`-morphisms on the nose. -/
@[simp]
theorem strictPseudofunctor.map_id
    (X : FiberedCategoryOver.{u, v, w, vS} C) :
    (strictPseudofunctor C).map (𝟙 X) =
      𝟙 ((strictPseudofunctor C).obj X) := sorry

/-- Strict fibred inertia preserves composition of `1`-morphisms on the
nose. -/
@[simp]
theorem strictPseudofunctor.map_comp
    {Z : FiberedCategoryOver.{u, v, w, vS} C}
    (F : X ⟶ Y) (G : Y ⟶ Z) :
    (strictPseudofunctor C).map (F ≫ G) =
      (strictPseudofunctor C).map F ≫
        (strictPseudofunctor C).map G := sorry

/-- The strict `2`-cell action is the canonical bundled inertia
transformation. -/
@[simp]
theorem strictPseudofunctor.map₂ {F G : X ⟶ Y} (τ : F ⟶ G) :
    (strictPseudofunctor C).map₂ τ = map₂ τ := sorry

/-- The semantic based-natural-transformation projection of the strict
fibred-inertia `2`-cell is the neutral inertia action. -/
@[simp]
theorem strictPseudofunctor.map₂.toBasedNatTrans
    {F G : X ⟶ Y} (τ : F ⟶ G) :
    FiberedCategoryOver.toBasedNatTrans ((strictPseudofunctor C).map₂ τ) =
      BasedCategory.Inertia.map₂ (FiberedCategoryOver.toBasedNatTrans τ) := sorry

end FiberedCategoryOver.Inertia

end CategoryTheory
