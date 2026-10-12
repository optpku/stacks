/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Pseudofunctor.Projections
public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.NatTrans
public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Lift.Computations
public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Pseudofunctor.Computations
public import ReasLib.CategoryTheory.Bicategory.LocallyInduced.Computations
public import ReasLib.CategoryTheory.Bicategory.LocallyInduced.Pseudofunctor.Computations

/-!
# Action computations for fibred inertia

This leaf identifies the object, local-hom, `1`-morphism, and `2`-morphism
fields of the ordinary fibred-inertia pseudofunctor with their reusable data
owners.  Because this pseudofunctor is the ordinary view of a strict owner,
its identity and composition actions are also exposed on the nose.
-/

@[expose] public section

universe u v vS w

namespace CategoryTheory

open BasedCategory BasedFunctor
open scoped Bicategory

namespace FiberedCategoryOver.Inertia

variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.{u, v, w, vS} C}

/-- The ordinary `1`-morphism action is the canonical bundled inertia map. -/
@[simp]
theorem pseudofunctor.map (F : X ⟶ Y) :
    (pseudofunctor C).map F = map F := sorry

/-- The based functor underlying ordinary fibred inertia is the neutral
inertia map. -/
@[simp]
theorem pseudofunctor.map.toBasedFunctor (F : X ⟶ Y) :
    FiberedCategoryOver.toBasedFunctor ((pseudofunctor C).map F) =
      BasedCategory.Inertia.map
        (FiberedCategoryOver.toBasedFunctor F) := sorry

/-- Ordinary fibred inertia preserves identity `1`-morphisms on the nose. -/
@[simp]
theorem pseudofunctor.map_id
    (X : FiberedCategoryOver.{u, v, w, vS} C) :
    (pseudofunctor C).map (𝟙 X) = 𝟙 ((pseudofunctor C).obj X) := sorry

/-- Ordinary fibred inertia preserves composition of `1`-morphisms on the
nose. -/
@[simp]
theorem pseudofunctor.map_comp
    {Z : FiberedCategoryOver.{u, v, w, vS} C}
    (F : X ⟶ Y) (G : Y ⟶ Z) :
    (pseudofunctor C).map (F ≫ G) =
      (pseudofunctor C).map F ≫ (pseudofunctor C).map G := sorry

/-- The ordinary `2`-morphism action is the canonical fibred-inertia
action. -/
@[simp]
theorem pseudofunctor.map₂ {F G : X ⟶ Y} (τ : F ⟶ G) :
    (pseudofunctor C).map₂ τ = map₂ τ := sorry

/-- The semantic based-natural-transformation projection of ordinary
fibred-inertia is the neutral inertia action. -/
@[simp]
theorem pseudofunctor.map₂.toBasedNatTrans
    {F G : X ⟶ Y} (τ : F ⟶ G) :
    FiberedCategoryOver.toBasedNatTrans ((pseudofunctor C).map₂ τ) =
      BasedCategory.Inertia.map₂ (FiberedCategoryOver.toBasedNatTrans τ) := sorry

/-- The ordinary local action is the canonical fibred-inertia map functor. -/
@[simp]
theorem pseudofunctor.mapFunctor
    (X Y : FiberedCategoryOver.{u, v, w, vS} C) :
    (pseudofunctor C).mapFunctor X Y = mapFunctor X Y := sorry

/-- Evaluating the ordinary local hom functor on a `1`-cell gives the
canonical cartesian inertia map. -/
@[simp]
theorem pseudofunctor.mapFunctor.obj (F : X ⟶ Y) :
    ((pseudofunctor C).mapFunctor X Y).obj F =
      FiberedCategoryOver.Inertia.map F := sorry

/-- Evaluating the ordinary local hom functor on a `2`-cell gives the
canonical cartesian inertia action. -/
@[simp]
theorem pseudofunctor.mapFunctor.map
    {F G : X ⟶ Y} (τ : F ⟶ G) :
    ((pseudofunctor C).mapFunctor X Y).map τ =
      FiberedCategoryOver.Inertia.map₂ τ := sorry

/-- Evaluating the ordinary local hom functor on a `1`-cell gives the neutral
inertia map at the based level. -/
@[simp]
theorem pseudofunctor.mapFunctor.obj.toBasedFunctor (F : X ⟶ Y) :
    FiberedCategoryOver.toBasedFunctor
        ((pseudofunctor C).mapFunctor X Y |>.obj F) =
      BasedCategory.Inertia.map
        (FiberedCategoryOver.toBasedFunctor F) := sorry

/-- The semantic based-natural-transformation projection of the ordinary
local action is the neutral inertia `2`-cell. -/
@[simp]
theorem pseudofunctor.mapFunctor.map.toBasedNatTrans
    {F G : X ⟶ Y} (τ : F ⟶ G) :
    FiberedCategoryOver.toBasedNatTrans
        ((pseudofunctor C).mapFunctor X Y |>.map τ) =
      BasedCategory.Inertia.map₂ (FiberedCategoryOver.toBasedNatTrans τ) := sorry

end FiberedCategoryOver.Inertia

end CategoryTheory
