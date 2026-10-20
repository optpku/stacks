module

public import ReasLib.CategoryTheory.Fibered.Inertia.ToInertia.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Computations for the relative-to-absolute inertia comparison

This leaf exposes the underlying neutral map, together with its object,
automorphism, and underlying-arrow formulas.
-/

@[expose] public section

universe u v u₁ v₁ u₁' v₁'

namespace CategoryTheory
namespace BasedCategory

open BasedCategory BasedFunctor BasedNatIso BasedNatTrans

variable {C : Type u} [Category.{v} C]

section ToInertia

variable {X : BasedCategory.{v₁, u₁} C} {Y : BasedCategory.{v₁', u₁'} C}

/-- The underlying functor of the based relative-to-absolute comparison is the canonical neutral
relative-inertia map induced by the defining square. -/
@[simp, stacks 04Z5 "relative-to-absolute inertia functor computation"]
theorem RelativeInertia.toInertia.toFunctor (F : X ⥤ᵇ Y) :
    (RelativeInertia.toInertia F).toFunctor =
      CategoryTheory.RelativeInertia.map (𝟭 X.obj) Y.p F.projectionIso := sorry

/-- The comparison retains the underlying source object. -/
@[simp, stacks 04Z5 "relative-to-absolute inertia object computation"]
theorem RelativeInertia.toInertia.toFunctor.obj
    (F : X ⥤ᵇ Y) (A : (relativeInertia F).obj) :
    ((RelativeInertia.toInertia F).toFunctor.obj A).obj =
      A.obj := sorry

/-- The comparison retains the selected automorphism. -/
@[simp, stacks 04Z5 "relative-to-absolute inertia automorphism computation"]
theorem RelativeInertia.toInertia.toFunctor.aut
    (F : X ⥤ᵇ Y) (A : (relativeInertia F).obj) :
    ((RelativeInertia.toInertia F).toFunctor.obj A).aut =
      A.aut := sorry

/-- The comparison retains the arrow underlying every morphism. -/
@[simp, stacks 04Z5 "relative-to-absolute inertia arrow computation"]
theorem RelativeInertia.toInertia.toFunctor.hom
    (F : X ⥤ᵇ Y) {A B : (relativeInertia F).obj} (f : A ⟶ B) :
    CategoryTheory.RelativeInertia.hom
        ((RelativeInertia.toInertia F).toFunctor.map f) =
      CategoryTheory.RelativeInertia.hom f := sorry

end ToInertia

end BasedCategory
end CategoryTheory
