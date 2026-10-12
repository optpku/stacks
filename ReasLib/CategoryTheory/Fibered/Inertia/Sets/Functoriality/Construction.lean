/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Sets.Objects.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.Map.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.NatTrans.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Typed inertia action for set-fibred categories

This leaf owns the direct `1`-cell and `2`-cell actions of set-fibred inertia.
The strict pseudofunctor remains the canonical structural owner; these definitions
provide the application-facing typed action at the same level as the groupoid and
setoid owners.
-/

@[expose] public section

universe u v vS w

namespace CategoryTheory

open BasedCategory BasedFunctor
open scoped Bicategory

namespace FiberedCategoryOver.Sets.Inertia

variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.Sets.{u, v, w, vS} C}

/-- The direct set-fibred inertia action on a `1`-morphism. -/
@[stacks 04Z4 "set-fibred inertia map"]
def map (F : X ⟶ Y) :
    FiberedCategoryOver.Sets.inertia X ⟶
      FiberedCategoryOver.Sets.inertia Y :=
  FiberedCategoryOver.Sets.ofBasedFunctor
    (BasedCategory.Inertia.map
      (FiberedCategoryOver.Sets.toBasedFunctor F))

/-- The direct set-fibred inertia action on a `2`-morphism. -/
@[stacks 04Z4 "set-fibred inertia two-cell map"]
def map₂ {F G : X ⟶ Y} (τ : F ⟶ G) :
    map F ⟶ map G :=
  FiberedCategoryOver.Sets.ofBasedNatTrans
    (BasedCategory.Inertia.map₂
      (FiberedCategoryOver.Sets.toBasedNatTrans τ))

namespace map₂

/-- Set-fibred inertia preserves identity `2`-morphisms. -/
@[simp, stacks 04Z4 "set-fibred inertia two-cell identity"]
theorem id (F : X ⟶ Y) :
    map₂ (𝟙 F) = 𝟙 (map F) := sorry

/-- Set-fibred inertia preserves vertical composition of `2`-morphisms. -/
@[simp, stacks 04Z4 "set-fibred inertia two-cell composition"]
theorem comp {F G H : X ⟶ Y} (τ : F ⟶ G) (σ : G ⟶ H) :
    map₂ (τ ≫ σ) = map₂ τ ≫ map₂ σ := sorry

end map₂

/-- The functor induced by set-fibred inertia on each hom category. -/
@[stacks 04Z4 "set-fibred inertia hom functor"]
def mapFunctor
    (X : FiberedCategoryOver.Sets.{u, v, w, vS} C)
    (Y : FiberedCategoryOver.Sets.{u, v, w, vS} C) :
    (X ⟶ Y) ⥤ (inertia X ⟶ inertia Y) where
  obj := map
  map := map₂
  map_id := map₂.id
  map_comp := map₂.comp

/-- The isomorphism induced by set-fibred inertia on a hom isomorphism. -/
@[stacks 04Z4 "set-fibred inertia hom isomorphism"]
def mapIso {F G : X ⟶ Y} (e : F ≅ G) :
    map F ≅ map G :=
  (mapFunctor X Y).mapIso e

end FiberedCategoryOver.Sets.Inertia

end CategoryTheory
