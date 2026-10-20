/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom
public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.Objects.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.Map.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.NatTrans.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Typed inertia action for groupoid-fibred categories

This leaf owns the concrete `1`-cell and `2`-cell actions of groupoid-fibred
inertia.  The actions are built directly from the neutral based owners and
the induced-bicategory constructors; the pseudofunctor fields are exposed in
the separate `AbsolutePseudofunctor` leaves.
-/

@[expose] public section

universe u v vS w

namespace CategoryTheory

open BasedCategory BasedFunctor
open scoped Bicategory

namespace FiberedCategoryOver.Groupoids.Inertia

variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.Groupoids.{u, v, w, vS} C}

/-- The direct groupoid-fibred inertia action on a `1`-morphism. -/
@[stacks 04Z4 "groupoid-fibred inertia map"]
def map (F : X ⟶ Y) :
    FiberedCategoryOver.Groupoids.inertia X ⟶
      FiberedCategoryOver.Groupoids.inertia Y :=
  FiberedCategoryOver.Groupoids.ofBasedFunctor
    (BasedCategory.Inertia.map
      (FiberedCategoryOver.Groupoids.toBasedFunctor F))

/-- The direct groupoid-fibred inertia action on a `2`-morphism. -/
@[stacks 04Z4 "groupoid-fibred inertia two-cell map"]
def map₂ {F G : X ⟶ Y} (τ : F ⟶ G) :
    map F ⟶ map G :=
  Bicategory.InducedBicategory.mkHom₂
    (BasedCategory.Inertia.map₂
      (FiberedCategoryOver.Groupoids.toBasedNatTrans τ))

namespace map₂

/-- Typed groupoid-fibred inertia preserves identity `2`-morphisms. -/
@[simp, stacks 04Z4 "groupoid-fibred inertia two-cell identity"]
theorem id (F : X ⟶ Y) :
    map₂ (𝟙 F) = 𝟙 (map F) := sorry

/-- Typed groupoid-fibred inertia preserves vertical composition of `2`-morphisms. -/
@[simp, stacks 04Z4 "groupoid-fibred inertia two-cell composition"]
theorem comp {F G H : X ⟶ Y} (τ : F ⟶ G) (σ : G ⟶ H) :
    map₂ (τ ≫ σ) = map₂ τ ≫ map₂ σ := sorry

end map₂

/-- The functor induced by groupoid-fibred inertia on each hom category. -/
@[stacks 04Z4 "groupoid-fibred inertia hom functor"]
def mapFunctor
    (X : FiberedCategoryOver.Groupoids.{u, v, w, vS} C)
    (Y : FiberedCategoryOver.Groupoids.{u, v, w, vS} C) :
    (X ⟶ Y) ⥤ (inertia X ⟶ inertia Y) where
  obj := map
  map := map₂
  map_id := map₂.id
  map_comp := map₂.comp

/-- The isomorphism induced by groupoid-fibred inertia on a hom isomorphism. -/
@[stacks 04Z4 "groupoid-fibred inertia hom isomorphism"]
def mapIso {F G : X ⟶ Y} (e : F ≅ G) :
    map F ≅ map G :=
  (mapFunctor X Y).mapIso e

end FiberedCategoryOver.Groupoids.Inertia

end CategoryTheory
