module

public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Specializations in Noetherian Schemes

Infinite subsets of Noetherian schemes contain infinite specialization antichains.
-/

@[expose] public section

open Set TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}}

/-- Every infinite subset of a Noetherian scheme contains an infinite subset whose points have no
nontrivial specializations among them. -/
theorem exists_infinite_subset_without_nontrivial_specializations
    [AlgebraicGeometry.IsNoetherian S] {T : Set S} (hT : T.Infinite) :
    ∃ T' ⊆ T, T'.Infinite ∧ IsAntichain (· ⤳ ·) T' := sorry

end AlgebraicGeometry.Scheme
