module

public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Forget.Construction

/-!
# Computations for cartesian forgetting from absolute inertia

This leaf exposes the based functor, total functor, object, and arrow underlying
the heterogeneous cartesian forgetful map.
-/

@[expose] public section

universe u v uS vS

namespace CategoryTheory.BasedCategory.Inertia

variable {C : Type u} [Category.{v} C]

/-- The based functor underlying cartesian inertia forgetting is the canonical neutral
forgetful map. -/
@[simp, stacks 042H "heterogeneous cartesian inertia forgetful based functor"]
theorem cartesianForget.toBasedFunctor
    (X : BasedCategory.{vS, uS} C) [X.p.IsFibered] :
    (cartesianForget X).toBasedFunctor = BasedCategory.Inertia.forget X := sorry

/-- The total functor underlying cartesian inertia forgetting is neutral inertia forgetting. -/
@[simp, stacks 042H "heterogeneous cartesian inertia forgetful total functor"]
theorem cartesianForget.toFunctor
    (X : BasedCategory.{vS, uS} C) [X.p.IsFibered] :
    (cartesianForget X).toFunctor =
      CategoryTheory.RelativeInertia.forget X.toBase.toFunctor := sorry

/-- Cartesian inertia forgetting returns the underlying object. -/
@[simp, stacks 042H "heterogeneous cartesian inertia forgetful object"]
theorem cartesianForget.obj
    (X : BasedCategory.{vS, uS} C) [X.p.IsFibered]
    (A : (BasedCategory.inertia X).obj) :
    (cartesianForget X).toFunctor.obj A = A.obj := sorry

/-- Cartesian inertia forgetting returns the underlying arrow. -/
@[simp, stacks 042H "heterogeneous cartesian inertia forgetful arrow"]
theorem cartesianForget.map
    (X : BasedCategory.{vS, uS} C) [X.p.IsFibered]
    {A B : (BasedCategory.inertia X).obj} (f : A ⟶ B) :
    (cartesianForget X).toFunctor.map f =
      CategoryTheory.RelativeInertia.hom f := sorry

end CategoryTheory.BasedCategory.Inertia
