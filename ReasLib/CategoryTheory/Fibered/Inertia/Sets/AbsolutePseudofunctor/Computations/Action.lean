/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Sets.AbsolutePseudofunctor.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Sets.Functoriality.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Sets.Objects.Construction

/-! # Action computations for set-fibred inertia -/

@[expose] public section
universe u v vS w
namespace CategoryTheory
open BasedCategory BasedFunctor
open scoped Bicategory
namespace FiberedCategoryOver.Sets.Inertia

variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.Sets.{u, v, w, vS} C}

namespace strictPseudofunctor

/-- The strict inertia pseudofunctor sends an object to its bundled set-fibred inertia. -/
@[simp] theorem obj (X : FiberedCategoryOver.Sets.{u, v, w, vS} C) :
    (strictPseudofunctor C).obj X = FiberedCategoryOver.Sets.inertia X := sorry

/-- The strict typed one-cell action is the direct set-fibred inertia owner. -/
@[simp] theorem map (F : X ⟶ Y) :
    (strictPseudofunctor C).map F = Inertia.map F := sorry

/-- The strict typed two-cell action is the direct set-fibred inertia owner. -/
@[simp] theorem map₂ {F G : X ⟶ Y} (τ : F ⟶ G) :
    (strictPseudofunctor C).map₂ τ = Inertia.map₂ τ := sorry

/-- The strict local hom action is the direct typed inertia hom functor. -/
@[simp] theorem mapFunctor
    (X Y : FiberedCategoryOver.Sets.{u, v, w, vS} C) :
    (strictPseudofunctor C).mapFunctor X Y = Inertia.mapFunctor X Y := sorry

/-- The strict local hom action evaluates on a `1`-cell to the direct typed inertia map. -/
@[simp] theorem mapFunctor.obj (F : X ⟶ Y) :
    ((strictPseudofunctor C).mapFunctor X Y).obj F = Inertia.map F := sorry

/-- The strict local hom action evaluates on a `2`-cell to the direct typed inertia action. -/
@[simp] theorem mapFunctor.map {F G : X ⟶ Y} (τ : F ⟶ G) :
    ((strictPseudofunctor C).mapFunctor X Y).map τ = Inertia.map₂ τ := sorry

/-- The based functor underlying the strict `1`-cell action is the neutral inertia map. -/
@[simp] theorem map.toBasedFunctor (F : X ⟶ Y) :
    FiberedCategoryOver.Sets.toBasedFunctor ((strictPseudofunctor C).map F) =
      BasedCategory.Inertia.map (FiberedCategoryOver.Sets.toBasedFunctor F) := sorry

/-- The strict action preserves identity `1`-cells on the nose. -/
@[simp] theorem map_id (X : FiberedCategoryOver.Sets.{u, v, w, vS} C) :
    (strictPseudofunctor C).map (𝟙 X) = 𝟙 ((strictPseudofunctor C).obj X) := sorry

/-- The strict action preserves composition on the nose. -/
@[simp] theorem map_comp {Z : FiberedCategoryOver.Sets.{u, v, w, vS} C}
    (F : X ⟶ Y) (G : Y ⟶ Z) :
    (strictPseudofunctor C).map (F ≫ G) =
      (strictPseudofunctor C).map F ≫ (strictPseudofunctor C).map G := sorry

/-- The based natural transformation underlying the strict `2`-cell action is the neutral inertia `2`-cell. -/
@[simp] theorem map₂.toBasedNatTrans {F G : X ⟶ Y} (eta : F ⟶ G) :
    FiberedCategoryOver.Sets.toBasedNatTrans ((strictPseudofunctor C).map₂ eta) =
      BasedCategory.Inertia.map₂ (FiberedCategoryOver.Sets.toBasedNatTrans eta) := sorry

/-- The object action of the strict local Hom functor has the neutral based inertia map. -/
@[simp] theorem mapFunctor.obj.toBasedFunctor (F : X ⟶ Y) :
    FiberedCategoryOver.Sets.toBasedFunctor
        ((strictPseudofunctor C).mapFunctor X Y |>.obj F) =
      BasedCategory.Inertia.map (FiberedCategoryOver.Sets.toBasedFunctor F) := sorry

/-- The morphism action of the strict local Hom functor has the neutral inertia `2`-cell. -/
@[simp] theorem mapFunctor.map.toBasedNatTrans {F G : X ⟶ Y} (eta : F ⟶ G) :
    FiberedCategoryOver.Sets.toBasedNatTrans
        ((strictPseudofunctor C).mapFunctor X Y |>.map eta) =
      BasedCategory.Inertia.map₂ (FiberedCategoryOver.Sets.toBasedNatTrans eta) := sorry

end strictPseudofunctor

namespace pseudofunctor

/-- The ordinary inertia pseudofunctor sends an object to its bundled set-fibred inertia. -/
@[simp] theorem obj (X : FiberedCategoryOver.Sets.{u, v, w, vS} C) :
    (pseudofunctor C).obj X = FiberedCategoryOver.Sets.inertia X := sorry

/-- The ordinary typed one-cell action is the direct set-fibred inertia owner. -/
@[simp] theorem map (F : X ⟶ Y) :
    (pseudofunctor C).map F = Inertia.map F := sorry

/-- The ordinary typed two-cell action is the direct set-fibred inertia owner. -/
@[simp] theorem map₂ {F G : X ⟶ Y} (τ : F ⟶ G) :
    (pseudofunctor C).map₂ τ = Inertia.map₂ τ := sorry

/-- The ordinary local hom action is the direct typed inertia hom functor. -/
@[simp] theorem mapFunctor
    (X Y : FiberedCategoryOver.Sets.{u, v, w, vS} C) :
    (pseudofunctor C).mapFunctor X Y = Inertia.mapFunctor X Y := sorry

/-- The ordinary local hom action evaluates on a `1`-cell to the direct typed inertia map. -/
@[simp] theorem mapFunctor.obj (F : X ⟶ Y) :
    ((pseudofunctor C).mapFunctor X Y).obj F = Inertia.map F := sorry

/-- The ordinary local hom action evaluates on a `2`-cell to the direct typed inertia action. -/
@[simp] theorem mapFunctor.map {F G : X ⟶ Y} (τ : F ⟶ G) :
    ((pseudofunctor C).mapFunctor X Y).map τ = Inertia.map₂ τ := sorry

/-- The based functor underlying the ordinary `1`-cell action is the neutral inertia map. -/
@[simp] theorem map.toBasedFunctor (F : X ⟶ Y) :
    FiberedCategoryOver.Sets.toBasedFunctor ((pseudofunctor C).map F) =
      BasedCategory.Inertia.map (FiberedCategoryOver.Sets.toBasedFunctor F) := sorry

/-- The ordinary action preserves identity `1`-cells on the nose. -/
@[simp] theorem map_id (X : FiberedCategoryOver.Sets.{u, v, w, vS} C) :
    (pseudofunctor C).map (𝟙 X) = 𝟙 ((pseudofunctor C).obj X) := sorry

/-- The ordinary action preserves composition on the nose. -/
@[simp] theorem map_comp {Z : FiberedCategoryOver.Sets.{u, v, w, vS} C}
    (F : X ⟶ Y) (G : Y ⟶ Z) :
    (pseudofunctor C).map (F ≫ G) =
      (pseudofunctor C).map F ≫ (pseudofunctor C).map G := sorry

/-- The based natural transformation underlying the ordinary `2`-cell action is the neutral inertia `2`-cell. -/
@[simp] theorem map₂.toBasedNatTrans {F G : X ⟶ Y} (eta : F ⟶ G) :
    FiberedCategoryOver.Sets.toBasedNatTrans ((pseudofunctor C).map₂ eta) =
      BasedCategory.Inertia.map₂ (FiberedCategoryOver.Sets.toBasedNatTrans eta) := sorry

/-- The object action of the ordinary local Hom functor has the neutral based inertia map. -/
@[simp] theorem mapFunctor.obj.toBasedFunctor (F : X ⟶ Y) :
    FiberedCategoryOver.Sets.toBasedFunctor
        ((pseudofunctor C).mapFunctor X Y |>.obj F) =
      BasedCategory.Inertia.map (FiberedCategoryOver.Sets.toBasedFunctor F) := sorry

/-- The morphism action of the ordinary local Hom functor has the neutral inertia `2`-cell. -/
@[simp] theorem mapFunctor.map.toBasedNatTrans {F G : X ⟶ Y} (eta : F ⟶ G) :
    FiberedCategoryOver.Sets.toBasedNatTrans
        ((pseudofunctor C).mapFunctor X Y |>.map eta) =
      BasedCategory.Inertia.map₂ (FiberedCategoryOver.Sets.toBasedNatTrans eta) := sorry

end pseudofunctor
end FiberedCategoryOver.Sets.Inertia
end CategoryTheory
