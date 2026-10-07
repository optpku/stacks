module

public import Mathlib.SetTheory.Cardinal.Cofinality.Ordinal

/-!
# Cofinality bounds inside an ordinal

This leaf packages `Ordinal.iSup_lt_of_lt_cof` in the order-theoretic language used by diagrams
indexed by `Ordinal.ToType`.
-/

@[expose] public section

universe v u

namespace Ordinal.ToType

/-- A family of fewer than `α.cof` stages of `α` has a common upper bound. -/
theorem exists_upperBound_of_lift_mk_lt_cof {S : Type v} {α : Ordinal.{u}}
    (hS : Cardinal.lift.{u} (Cardinal.mk S) < Cardinal.lift.{v} α.cof)
    (f : S → α.ToType) :
    ∃ j : α.ToType, ∀ s : S, f s ≤ j := sorry

/-- Same-universe form of `exists_upperBound_of_lift_mk_lt_cof`. -/
theorem exists_upperBound_of_mk_lt_cof {S : Type u} {α : Ordinal.{u}}
    (hS : Cardinal.mk S < α.cof) (f : S → α.ToType) :
    ∃ j : α.ToType, ∀ s : S, f s ≤ j := sorry

end Ordinal.ToType
