/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Map.Absolute.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.NatTrans.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Construction of the cartesian inertia `2`-cell action

This file owns the bundled cartesian `2`-cell action, the local hom functor, and the induced
isomorphism. Projection formulas, component calculations, and whiskering laws are layered in
the companion computation leaves.
-/

@[expose] public section

universe u v uS vS w

namespace CategoryTheory

open BasedCategory BasedFunctor
open scoped Bicategory

namespace FiberedCategoryOver.Inertia

variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.{u, v, w, vS} C}

/- A `2`-cell is lifted through the cartesian owner of the absolute inertia map. -/

/-- A `2`-morphism between morphisms of fibred categories induces the canonical
`2`-morphism between their cartesian inertia maps. -/
@[stacks 04Z4 "cartesian absolute-inertia action on 2-morphisms"]
def map₂ {F G : X ⟶ Y} (τ : F ⟶ G) :
    map F ⟶ map G :=
  ObjectProperty.homMk
    (BasedCategory.Inertia.map₂ (FiberedCategoryOver.toBasedNatTrans τ))

namespace map₂

/-- The cartesian inertia action preserves identity `2`-morphisms. -/
@[simp, stacks 04Z4 "cartesian inertia two-cell identity"]
theorem id (F : X ⟶ Y) :
    map₂ (𝟙 F) = 𝟙 (map F) := sorry

/-- The cartesian inertia action preserves vertical composition of `2`-morphisms. -/
@[simp, stacks 04Z4 "cartesian inertia two-cell composition"]
theorem comp {F G H : X ⟶ Y} (τ : F ⟶ G) (σ : G ⟶ H) :
    map₂ (τ ≫ σ) = map₂ τ ≫ map₂ σ := sorry

end map₂

/-- Inertia acts functorially on each hom category of fibred categories. -/
@[stacks 04Z4 "cartesian absolute-inertia local hom functor"]
def mapFunctor
    (X : FiberedCategoryOver.{u, v, w, vS} C)
    (Y : FiberedCategoryOver.{u, v, w, vS} C) :
    (X ⟶ Y) ⥤
      (FiberedCategoryOver.inertia X ⟶ FiberedCategoryOver.inertia Y) where
  obj := map
  map := map₂
  map_id := map₂.id
  map_comp := map₂.comp

/-- An isomorphism between morphisms of fibred categories induces an isomorphism between their
cartesian inertia maps. -/
@[stacks 04Z4 "cartesian absolute-inertia action on invertible 2-morphisms"]
def mapIso {F G : X ⟶ Y} (e : F ≅ G) :
    map F ≅ map G :=
  (mapFunctor X Y).mapIso e

end FiberedCategoryOver.Inertia

end CategoryTheory

/- Axiom audit: the data owners are deterministic lifts of the neutral inertia action; deferred
proofs occur only in the cartesian owner and coherence fields. -/
