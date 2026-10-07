module

public import Mathlib.CategoryTheory.FiberedCategory.Fibered
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Equivalence.Basic
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Fiber

/-!
# Fiberwise criteria for cartesian based functors

Faithfulness and full faithfulness of a cartesian based functor with fibred source can be checked
on the standard fibers. When both projections are fibred, the same is true for equivalence over
the base. The total categories may live in independent universes, and no cleavage is selected.
-/

@[expose] public section

universe uC vC uS vS uT vT

namespace CategoryTheory

variable {C : Type uC} [Category.{vC} C]
variable {S : Type uS} {T : Type uT}
variable [Category.{vS} S] [Category.{vT} T]
variable {pS : S ⥤ C} {pT : T ⥤ C}

namespace CartesianBasedFunctor

/-- A cartesian based functor with fibred source is faithful on total categories exactly when it
is faithful on every standard fiber. -/
theorem faithful_iff_fiberwise [pS.IsFibered]
    (F : CartesianBasedFunctor pS pT) :
    (F.toFunctor).Faithful ↔ ∀ U : C, (F.fiberFunctor U).Faithful := sorry

/-- A cartesian based functor with fibred source is fully faithful on total categories exactly
when it is fully faithful on every standard fiber. -/
theorem fullyFaithful_iff_fiberwise [pS.IsFibered]
    (F : CartesianBasedFunctor pS pT) :
    Nonempty (F.toFunctor).FullyFaithful ↔
      ∀ U : C, Nonempty (F.fiberFunctor U).FullyFaithful := sorry

/-- For a cartesian based functor between fibred projections, equivalence over the base is
equivalent to equivalence on every standard fiber. -/
theorem isEquivalence_iff_fiberwise [pS.IsFibered] [pT.IsFibered]
    (F : CartesianBasedFunctor pS pT) :
    (F.toBasedFunctor).IsEquivalence ↔
      ∀ U : C, (F.fiberFunctor U).IsEquivalence := sorry

end CartesianBasedFunctor

end CategoryTheory
