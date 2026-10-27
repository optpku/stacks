/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Setoids.AbsolutePseudofunctor.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Setoids.Functoriality.Construction

/-! # Action computations for setoid-fibred inertia -/

@[expose] public section
universe u v vS w
namespace CategoryTheory
open BasedCategory BasedFunctor
open scoped Bicategory
namespace FiberedCategoryOver.Setoids.Inertia

variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.Setoids.{u, v, w, vS} C}

namespace strictPseudofunctor

/-- The strict setoid-fibred inertia pseudofunctor sends an object to its bundled inertia. -/
@[simp] theorem obj (X : FiberedCategoryOver.Setoids.{u, v, w, vS} C) :
    (strictPseudofunctor C).obj X = FiberedCategoryOver.Setoids.inertia X := rfl

/-- The strict typed one-cell action is the direct setoid-fibred inertia owner. -/
@[simp] theorem map (F : X ⟶ Y) :
    (strictPseudofunctor C).map F = Inertia.map F := rfl

/-- The strict typed two-cell action is the direct setoid-fibred inertia owner. -/
@[simp] theorem map₂ {F G : X ⟶ Y} (τ : F ⟶ G) :
    (strictPseudofunctor C).map₂ τ = Inertia.map₂ τ := rfl

/-- The strict local hom action is the direct typed inertia hom functor. -/
@[simp] theorem mapFunctor
    (X Y : FiberedCategoryOver.Setoids.{u, v, w, vS} C) :
    (strictPseudofunctor C).mapFunctor X Y = Inertia.mapFunctor X Y := rfl

/-- The strict local hom action evaluates on a `1`-cell to the direct typed inertia map. -/
@[simp] theorem mapFunctor.obj (F : X ⟶ Y) :
    ((strictPseudofunctor C).mapFunctor X Y).obj F = Inertia.map F := rfl

/-- The strict local hom action evaluates on a `2`-cell to the direct typed inertia action. -/
@[simp] theorem mapFunctor.map {F G : X ⟶ Y} (τ : F ⟶ G) :
    ((strictPseudofunctor C).mapFunctor X Y).map τ = Inertia.map₂ τ := rfl

/-- The based functor underlying the strict `1`-cell action is the neutral inertia map. -/
@[simp] theorem map.toBasedFunctor (F : X ⟶ Y) :
    FiberedCategoryOver.Setoids.toBasedFunctor ((strictPseudofunctor C).map F) =
      BasedCategory.Inertia.map (FiberedCategoryOver.Setoids.toBasedFunctor F) := rfl

/-- The strict setoid-fibred inertia action preserves identity `1`-cells on the nose. -/
@[simp] theorem map_id (X : FiberedCategoryOver.Setoids.{u, v, w, vS} C) :
    (strictPseudofunctor C).map (𝟙 X) = 𝟙 ((strictPseudofunctor C).obj X) := rfl

/-- The strict setoid-fibred inertia action preserves composition on the nose. -/
@[simp] theorem map_comp {Z : FiberedCategoryOver.Setoids.{u, v, w, vS} C}
    (F : X ⟶ Y) (G : Y ⟶ Z) :
    (strictPseudofunctor C).map (F ≫ G) =
      (strictPseudofunctor C).map F ≫ (strictPseudofunctor C).map G := rfl

/-- The based natural transformation underlying the strict `2`-cell action is the neutral inertia `2`-cell. -/
@[simp] theorem map₂.toBasedNatTrans {F G : X ⟶ Y} (τ : F ⟶ G) :
    FiberedCategoryOver.Setoids.toBasedNatTrans ((strictPseudofunctor C).map₂ τ) =
      BasedCategory.Inertia.map₂ (FiberedCategoryOver.Setoids.toBasedNatTrans τ) := rfl

/-- Evaluating the strict local hom functor on a `1`-cell has the neutral inertia map underneath. -/
@[simp] theorem mapFunctor.obj.toBasedFunctor (F : X ⟶ Y) :
    FiberedCategoryOver.Setoids.toBasedFunctor
        ((strictPseudofunctor C).mapFunctor X Y |>.obj F) =
      BasedCategory.Inertia.map (FiberedCategoryOver.Setoids.toBasedFunctor F) := rfl

/-- Evaluating the strict local hom functor on a `2`-cell has the neutral inertia `2`-cell underneath. -/
@[simp] theorem mapFunctor.map.toBasedNatTrans {F G : X ⟶ Y} (τ : F ⟶ G) :
    FiberedCategoryOver.Setoids.toBasedNatTrans
        ((strictPseudofunctor C).mapFunctor X Y |>.map τ) =
      BasedCategory.Inertia.map₂ (FiberedCategoryOver.Setoids.toBasedNatTrans τ) := rfl

end strictPseudofunctor

namespace pseudofunctor

/-- The ordinary typed one-cell action is the direct setoid-fibred inertia owner. -/
@[simp] theorem map (F : X ⟶ Y) :
    (pseudofunctor C).map F = Inertia.map F := rfl

/-- The ordinary typed two-cell action is the direct setoid-fibred inertia owner. -/
@[simp] theorem map₂ {F G : X ⟶ Y} (τ : F ⟶ G) :
    (pseudofunctor C).map₂ τ = Inertia.map₂ τ := rfl

/-- The ordinary local hom action is the direct typed inertia hom functor. -/
@[simp] theorem mapFunctor
    (X Y : FiberedCategoryOver.Setoids.{u, v, w, vS} C) :
    (pseudofunctor C).mapFunctor X Y = Inertia.mapFunctor X Y := rfl

/-- The ordinary local hom action evaluates on a `1`-cell to the direct typed inertia map. -/
@[simp] theorem mapFunctor.obj (F : X ⟶ Y) :
    ((pseudofunctor C).mapFunctor X Y).obj F = Inertia.map F := rfl

/-- The ordinary local hom action evaluates on a `2`-cell to the direct typed inertia action. -/
@[simp] theorem mapFunctor.map {F G : X ⟶ Y} (τ : F ⟶ G) :
    ((pseudofunctor C).mapFunctor X Y).map τ = Inertia.map₂ τ := rfl

/-- The based functor underlying the ordinary `1`-cell action is the neutral inertia map. -/
@[simp] theorem map.toBasedFunctor (F : X ⟶ Y) :
    FiberedCategoryOver.Setoids.toBasedFunctor ((pseudofunctor C).map F) =
      BasedCategory.Inertia.map (FiberedCategoryOver.Setoids.toBasedFunctor F) := rfl

/-- The ordinary setoid-fibred inertia action preserves identity `1`-cells on the nose. -/
@[simp] theorem map_id (X : FiberedCategoryOver.Setoids.{u, v, w, vS} C) :
    (pseudofunctor C).map (𝟙 X) = 𝟙 ((pseudofunctor C).obj X) := rfl

/-- The ordinary setoid-fibred inertia action preserves composition on the nose. -/
@[simp] theorem map_comp {Z : FiberedCategoryOver.Setoids.{u, v, w, vS} C}
    (F : X ⟶ Y) (G : Y ⟶ Z) :
    (pseudofunctor C).map (F ≫ G) =
      (pseudofunctor C).map F ≫ (pseudofunctor C).map G := rfl

/-- The based natural transformation underlying the ordinary `2`-cell action is the neutral inertia `2`-cell. -/
@[simp] theorem map₂.toBasedNatTrans {F G : X ⟶ Y} (τ : F ⟶ G) :
    FiberedCategoryOver.Setoids.toBasedNatTrans ((pseudofunctor C).map₂ τ) =
      BasedCategory.Inertia.map₂ (FiberedCategoryOver.Setoids.toBasedNatTrans τ) := rfl

/-- Evaluation of the ordinary local hom functor on a `1`-cell has the neutral inertia map underneath. -/
@[simp] theorem mapFunctor.obj.toBasedFunctor (F : X ⟶ Y) :
    FiberedCategoryOver.Setoids.toBasedFunctor
        ((pseudofunctor C).mapFunctor X Y |>.obj F) =
      BasedCategory.Inertia.map (FiberedCategoryOver.Setoids.toBasedFunctor F) := rfl

/-- Evaluation of the ordinary local hom functor on a `2`-cell has the neutral inertia `2`-cell underneath. -/
@[simp] theorem mapFunctor.map.toBasedNatTrans {F G : X ⟶ Y} (τ : F ⟶ G) :
    FiberedCategoryOver.Setoids.toBasedNatTrans
        ((pseudofunctor C).mapFunctor X Y |>.map τ) =
      BasedCategory.Inertia.map₂ (FiberedCategoryOver.Setoids.toBasedNatTrans τ) := rfl

end pseudofunctor
end FiberedCategoryOver.Setoids.Inertia
end CategoryTheory
