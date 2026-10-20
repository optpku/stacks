module

public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.NatTrans.Computations

/-!
# Local-functor and isomorphism computations for cartesian inertia

This leaf records the hom-functor and hom-isomorphism projections of the bundled cartesian
inertia action.
-/

@[expose] public section

universe u v uS vS w

namespace CategoryTheory

open BasedCategory BasedFunctor
open scoped Bicategory

namespace FiberedCategoryOver.Inertia

variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.{u, v, w, vS} C}

namespace mapFunctor

/-- The object action of the cartesian inertia hom functor is the canonical bundled map. -/
@[simp]
theorem obj (F : X ⟶ Y) :
    (mapFunctor X Y).obj F = map F := sorry

/-- The morphism action of the cartesian inertia hom functor is the canonical bundled `2`-cell. -/
@[simp]
theorem map {F G : X ⟶ Y} (τ : F ⟶ G) :
    (mapFunctor X Y).map τ = map₂ τ := sorry

end mapFunctor

namespace mapIso

/-- The forward action on a hom isomorphism is the forward cartesian inertia `2`-cell. -/
@[simp]
theorem hom {F G : X ⟶ Y} (e : F ≅ G) :
    (mapIso e).hom = map₂ e.hom := sorry

/-- The inverse action on a hom isomorphism is the inverse cartesian inertia `2`-cell. -/
@[simp]
theorem inv {F G : X ⟶ Y} (e : F ≅ G) :
    (mapIso e).inv = map₂ e.inv := sorry

end mapIso

end FiberedCategoryOver.Inertia

end CategoryTheory
