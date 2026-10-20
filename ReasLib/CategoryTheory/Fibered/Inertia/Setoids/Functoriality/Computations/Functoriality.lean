module

public import ReasLib.CategoryTheory.Fibered.Inertia.Setoids.Functoriality.Computations.TwoCell

/-!
# Hom-functor and isomorphism computations for typed setoid-fibred inertia

This leaf records the local hom functor and its action on isomorphisms,
including component-level readouts.
-/

@[expose] public section

universe u v vS w

namespace CategoryTheory

open BasedCategory BasedFunctor
open scoped Bicategory

namespace FiberedCategoryOver.Setoids.Inertia

variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.Setoids.{u, v, w, vS} C}

namespace mapFunctor

/-- The object action of the typed local hom functor is `map`. -/
@[simp]
theorem obj (F : X ⟶ Y) :
    (mapFunctor X Y).obj F = map F := sorry

/-- The morphism action of the typed local hom functor is `map₂`. -/
@[simp]
theorem map {F G : X ⟶ Y} (τ : F ⟶ G) :
    (mapFunctor X Y).map τ = map₂ τ := sorry

/-- The typed local hom action has the neutral component readout. -/
@[simp]
theorem map.app {F G : X ⟶ Y} (τ : F ⟶ G) (A : X.inertia.total) :
    (FiberedCategoryOver.Setoids.toNatTrans
      ((mapFunctor X Y).map τ)).app A =
      BasedCategory.Inertia.map₂.component
        (FiberedCategoryOver.Setoids.toBasedNatTrans τ) A := sorry

/-- Every typed local hom-action component is vertical over the identity on the base. -/
theorem map.app.isHomLift {F G : X ⟶ Y} (τ : F ⟶ G) (A : X.inertia.total) :
    Y.inertia.p.IsHomLift (𝟙 (X.inertia.p.obj A))
      ((FiberedCategoryOver.Setoids.toNatTrans
        ((mapFunctor X Y).map τ)).app A) := sorry

/-- The typed local hom-action component has the original underlying arrow. -/
@[simp]
theorem map.app.underlying {F G : X ⟶ Y} (τ : F ⟶ G) (A : X.inertia.total) :
    RelativeInertia.hom
        ((FiberedCategoryOver.Setoids.toNatTrans
          ((mapFunctor X Y).map τ)).app A) =
      (FiberedCategoryOver.Setoids.toNatTrans τ).app A.obj := sorry

end mapFunctor

namespace mapIso

/-- The forward action on an isomorphism is the forward typed inertia `2`-cell. -/
@[simp]
theorem hom {F G : X ⟶ Y} (e : F ≅ G) :
    (mapIso e).hom = map₂ e.hom := sorry

/-- The inverse action on an isomorphism is the inverse typed inertia `2`-cell. -/
@[simp]
theorem inv {F G : X ⟶ Y} (e : F ≅ G) :
    (mapIso e).inv = map₂ e.inv := sorry

/-- The forward component of a typed inertia isomorphism is the neutral component. -/
@[simp]
theorem hom.app {F G : X ⟶ Y} (e : F ≅ G) (A : X.inertia.total) :
    (FiberedCategoryOver.Setoids.toNatTrans (mapIso e).hom).app A =
      BasedCategory.Inertia.map₂.component
        (FiberedCategoryOver.Setoids.toBasedNatTrans e.hom) A := sorry

/-- The inverse component of a typed inertia isomorphism is the neutral component. -/
@[simp]
theorem inv.app {F G : X ⟶ Y} (e : F ≅ G) (A : X.inertia.total) :
    (FiberedCategoryOver.Setoids.toNatTrans (mapIso e).inv).app A =
      BasedCategory.Inertia.map₂.component
        (FiberedCategoryOver.Setoids.toBasedNatTrans e.inv) A := sorry

/-- The underlying arrow of a forward typed inertia-isomorphism component is the
original 2-cell component. -/
@[simp]
theorem hom.app.underlying {F G : X ⟶ Y} (e : F ≅ G) (A : X.inertia.total) :
    RelativeInertia.hom
        ((FiberedCategoryOver.Setoids.toNatTrans (mapIso e).hom).app A) =
      (FiberedCategoryOver.Setoids.toNatTrans e.hom).app A.obj := sorry

/-- Every forward typed inertia-isomorphism component is vertical over the identity on the base. -/
theorem hom.app.isHomLift {F G : X ⟶ Y} (e : F ≅ G) (A : X.inertia.total) :
    Y.inertia.p.IsHomLift (𝟙 (X.inertia.p.obj A))
      ((FiberedCategoryOver.Setoids.toNatTrans (mapIso e).hom).app A) := sorry

/-- The underlying arrow of an inverse typed inertia-isomorphism component is the
original inverse 2-cell component. -/
@[simp]
theorem inv.app.underlying {F G : X ⟶ Y} (e : F ≅ G) (A : X.inertia.total) :
    RelativeInertia.hom
        ((FiberedCategoryOver.Setoids.toNatTrans (mapIso e).inv).app A) =
      (FiberedCategoryOver.Setoids.toNatTrans e.inv).app A.obj := sorry

/-- Every inverse typed inertia-isomorphism component is vertical over the identity on the base. -/
theorem inv.app.isHomLift {F G : X ⟶ Y} (e : F ≅ G) (A : X.inertia.total) :
    Y.inertia.p.IsHomLift (𝟙 (X.inertia.p.obj A))
      ((FiberedCategoryOver.Setoids.toNatTrans (mapIso e).inv).app A) := sorry

end mapIso

end FiberedCategoryOver.Setoids.Inertia

end CategoryTheory
