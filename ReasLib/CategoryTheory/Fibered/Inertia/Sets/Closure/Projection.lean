module

public import ReasLib.CategoryTheory.Fibered.InSets
public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.Closure.Projection
import Mathlib.Tactic.CrossRefAttribute

/-!
# Set-fibred projection closure

This leaf owns the explicit relative and absolute projection instances for
discrete fibrations.
-/

@[expose] public section

universe u v uS vS uT vT

namespace CategoryTheory

open BasedCategory BasedFunctor

namespace RelativeInertia.Projection.Sets

variable {C : Type u} [Category.{v} C]
variable {S : Type uS} [Category.{vS} S]
variable {T : Type uT} [Category.{vT} T]
variable {p : S ⥤ C} {q : T ⥤ C}

/-- The relative-inertia projection of cartesian functors between discrete fibrations is a
discrete fibration. -/
@[stacks 04Z4 "set-fibred relative-inertia closure"]
theorem ofCartesian
    [Functor.IsDiscreteFibration p] [Functor.IsDiscreteFibration q]
    (F : CartesianBasedFunctor p q) :
    Functor.IsDiscreteFibration
      (RelativeInertia.projection F.toFunctor p) := sorry

/-- The self-relative-inertia projection of a discrete fibration is again a discrete
fibration. -/
theorem self (p : S ⥤ C) [Functor.IsDiscreteFibration p] :
    Functor.IsDiscreteFibration (RelativeInertia.projection p p) := sorry

end RelativeInertia.Projection.Sets

namespace BasedCategory.Inertia.Projection.Sets

variable {C : Type u} [Category.{v} C]

/-- The projection from neutral based absolute inertia is a discrete fibration whenever the
original projection is. -/
instance self
    (X : BasedCategory.{vS, uS} C) [Functor.IsDiscreteFibration X.p] :
    Functor.IsDiscreteFibration (BasedCategory.inertia X).p := sorry

end BasedCategory.Inertia.Projection.Sets

end CategoryTheory
