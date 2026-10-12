/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.AbsolutePseudofunctor.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.Functoriality.Construction

/-! # Action computations for groupoid-fibred inertia -/

@[expose] public section

universe u v vS w

namespace CategoryTheory
open BasedCategory BasedFunctor
open scoped Bicategory
namespace FiberedCategoryOver.Groupoids.Inertia

variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.Groupoids.{u, v, w, vS} C}

namespace strictPseudofunctor

/-- The strict groupoid-fibred inertia pseudofunctor sends an object to its bundled inertia. -/
@[simp] theorem obj (X : FiberedCategoryOver.Groupoids.{u, v, w, vS} C) :
    (strictPseudofunctor C).obj X = FiberedCategoryOver.Groupoids.inertia X := sorry

/-- The strict typed one-cell action is the direct groupoid-fibred inertia owner. -/
@[simp] theorem map (F : X ⟶ Y) :
    (strictPseudofunctor C).map F = Inertia.map F := sorry

/-- The strict typed two-cell action is the direct groupoid-fibred inertia owner. -/
@[simp] theorem map₂ {F G : X ⟶ Y} (τ : F ⟶ G) :
    (strictPseudofunctor C).map₂ τ = Inertia.map₂ τ := sorry

/-- The strict local hom action is the direct typed inertia hom functor. -/
@[simp] theorem mapFunctor
    (X Y : FiberedCategoryOver.Groupoids.{u, v, w, vS} C) :
    (strictPseudofunctor C).mapFunctor X Y = Inertia.mapFunctor X Y := sorry

/-- The strict local hom action evaluates on a `1`-cell to the direct typed inertia map. -/
@[simp] theorem mapFunctor.obj (F : X ⟶ Y) :
    ((strictPseudofunctor C).mapFunctor X Y).obj F = Inertia.map F := sorry

/-- The strict local hom action evaluates on a `2`-cell to the direct typed inertia action. -/
@[simp] theorem mapFunctor.map {F G : X ⟶ Y} (τ : F ⟶ G) :
    ((strictPseudofunctor C).mapFunctor X Y).map τ = Inertia.map₂ τ := sorry

/-- The based functor underlying the strict `1`-cell action is the neutral inertia map. -/
@[simp] theorem map.toBasedFunctor (F : X ⟶ Y) :
    FiberedCategoryOver.Groupoids.toBasedFunctor ((strictPseudofunctor C).map F) =
      BasedCategory.Inertia.map (FiberedCategoryOver.Groupoids.toBasedFunctor F) := sorry

/-- The strict groupoid-fibred inertia action preserves identity `1`-cells on the nose. -/
@[simp] theorem map_id (X : FiberedCategoryOver.Groupoids.{u, v, w, vS} C) :
    (strictPseudofunctor C).map (𝟙 X) = 𝟙 ((strictPseudofunctor C).obj X) := sorry

/-- The strict groupoid-fibred inertia action preserves composition on the nose. -/
@[simp] theorem map_comp {Z : FiberedCategoryOver.Groupoids.{u, v, w, vS} C}
    (F : X ⟶ Y) (G : Y ⟶ Z) :
    (strictPseudofunctor C).map (F ≫ G) =
      (strictPseudofunctor C).map F ≫ (strictPseudofunctor C).map G := sorry

/-- The based natural transformation underlying the strict `2`-cell action is the neutral inertia `2`-cell. -/
@[simp] theorem map₂.toBasedNatTrans {F G : X ⟶ Y} (τ : F ⟶ G) :
    FiberedCategoryOver.Groupoids.toBasedNatTrans ((strictPseudofunctor C).map₂ τ) =
      BasedCategory.Inertia.map₂ (FiberedCategoryOver.Groupoids.toBasedNatTrans τ) := sorry

/-- Evaluating the strict local hom functor on a `1`-cell has the neutral inertia map underneath. -/
@[simp] theorem mapFunctor.obj.toBasedFunctor (F : X ⟶ Y) :
    FiberedCategoryOver.Groupoids.toBasedFunctor
        ((strictPseudofunctor C).mapFunctor X Y |>.obj F) =
      BasedCategory.Inertia.map (FiberedCategoryOver.Groupoids.toBasedFunctor F) := sorry

/-- Evaluating the strict local hom functor on a `2`-cell has the neutral inertia `2`-cell underneath. -/
@[simp] theorem mapFunctor.map.toBasedNatTrans {F G : X ⟶ Y} (τ : F ⟶ G) :
    FiberedCategoryOver.Groupoids.toBasedNatTrans
        ((strictPseudofunctor C).mapFunctor X Y |>.map τ) =
      BasedCategory.Inertia.map₂ (FiberedCategoryOver.Groupoids.toBasedNatTrans τ) := sorry

end strictPseudofunctor

namespace pseudofunctor

/-- The ordinary typed one-cell action is the direct groupoid-fibred inertia owner. -/
@[simp] theorem map (F : X ⟶ Y) :
    (pseudofunctor C).map F = Inertia.map F := sorry

/-- The ordinary typed two-cell action is the direct groupoid-fibred inertia owner. -/
@[simp] theorem map₂ {F G : X ⟶ Y} (τ : F ⟶ G) :
    (pseudofunctor C).map₂ τ = Inertia.map₂ τ := sorry

/-- The ordinary local hom action is the direct typed inertia hom functor. -/
@[simp] theorem mapFunctor
    (X Y : FiberedCategoryOver.Groupoids.{u, v, w, vS} C) :
    (pseudofunctor C).mapFunctor X Y = Inertia.mapFunctor X Y := sorry

/-- The ordinary local hom action evaluates on a `1`-cell to the direct typed inertia map. -/
@[simp] theorem mapFunctor.obj (F : X ⟶ Y) :
    ((pseudofunctor C).mapFunctor X Y).obj F = Inertia.map F := sorry

/-- The ordinary local hom action evaluates on a `2`-cell to the direct typed inertia action. -/
@[simp] theorem mapFunctor.map {F G : X ⟶ Y} (τ : F ⟶ G) :
    ((pseudofunctor C).mapFunctor X Y).map τ = Inertia.map₂ τ := sorry

/-- The based functor underlying the ordinary `1`-cell action is the neutral inertia map. -/
@[simp] theorem map.toBasedFunctor (F : X ⟶ Y) :
    FiberedCategoryOver.Groupoids.toBasedFunctor ((pseudofunctor C).map F) =
      BasedCategory.Inertia.map (FiberedCategoryOver.Groupoids.toBasedFunctor F) := sorry

/-- The ordinary groupoid-fibred inertia action preserves identity `1`-cells on the nose. -/
@[simp] theorem map_id (X : FiberedCategoryOver.Groupoids.{u, v, w, vS} C) :
    (pseudofunctor C).map (𝟙 X) = 𝟙 ((pseudofunctor C).obj X) := sorry

/-- The ordinary groupoid-fibred inertia action preserves composition on the nose. -/
@[simp] theorem map_comp {Z : FiberedCategoryOver.Groupoids.{u, v, w, vS} C}
    (F : X ⟶ Y) (G : Y ⟶ Z) :
    (pseudofunctor C).map (F ≫ G) =
      (pseudofunctor C).map F ≫ (pseudofunctor C).map G := sorry

/-- The based natural transformation underlying the ordinary `2`-cell action is the neutral inertia `2`-cell. -/
@[simp] theorem map₂.toBasedNatTrans {F G : X ⟶ Y} (τ : F ⟶ G) :
    FiberedCategoryOver.Groupoids.toBasedNatTrans ((pseudofunctor C).map₂ τ) =
      BasedCategory.Inertia.map₂ (FiberedCategoryOver.Groupoids.toBasedNatTrans τ) := sorry

/-- Evaluation of the ordinary local hom functor on a `1`-cell has the neutral inertia map underneath. -/
@[simp] theorem mapFunctor.obj.toBasedFunctor (F : X ⟶ Y) :
    FiberedCategoryOver.Groupoids.toBasedFunctor
        ((pseudofunctor C).mapFunctor X Y |>.obj F) =
      BasedCategory.Inertia.map (FiberedCategoryOver.Groupoids.toBasedFunctor F) := sorry

/-- Evaluation of the ordinary local hom functor on a `2`-cell has the neutral inertia `2`-cell underneath. -/
@[simp] theorem mapFunctor.map.toBasedNatTrans {F G : X ⟶ Y} (τ : F ⟶ G) :
    FiberedCategoryOver.Groupoids.toBasedNatTrans
        ((pseudofunctor C).mapFunctor X Y |>.map τ) =
      BasedCategory.Inertia.map₂ (FiberedCategoryOver.Groupoids.toBasedNatTrans τ) := sorry

end pseudofunctor
end FiberedCategoryOver.Groupoids.Inertia
end CategoryTheory
