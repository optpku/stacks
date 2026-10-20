module

public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Pseudofunctor.Relative.Action.Functoriality.Construction

/-!
# Functoriality computations for fibred relative inertia
-/

@[expose] public section

universe u v vS w

namespace CategoryTheory

open BasedCategory BasedFunctor
open Bicategory
open scoped Bicategory

namespace FiberedCategoryOver.RelativeInertia.pseudoComma

variable {C : Type u} [Category.{v} C]

variable
    {S T : Bicategory.PseudoComma
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))}

noncomputable section

namespace mapFunctor

/-- The object action of the local fibred relative-inertia functor is the square-induced map. -/
@[simp]
theorem obj (f : S ⟶ T) :
    (mapFunctor S T).obj f = map f := sorry

/-- The morphism action of the local fibred relative-inertia functor is the canonical induced
`2`-morphism. -/
@[simp]
theorem map {f g : S ⟶ T} (eta : f ⟶ g) :
    (mapFunctor S T).map eta = map₂ eta := sorry

end mapFunctor

namespace mapIso

/-- The forward cell of an induced relative-inertia isomorphism is the action on the forward
pseudo-comma cell. -/
@[simp]
theorem hom {f g : S ⟶ T} (e : f ≅ g) :
    (mapIso e).hom = map₂ e.hom := sorry

/-- The inverse cell of an induced relative-inertia isomorphism is the action on the inverse
pseudo-comma cell. -/
@[simp]
theorem inv {f g : S ⟶ T} (e : f ≅ g) :
    (mapIso e).inv = map₂ e.inv := sorry

end mapIso

end

end FiberedCategoryOver.RelativeInertia.pseudoComma
end CategoryTheory
