module

public import Mathlib.FieldTheory.RatFunc.IntermediateField
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

namespace RatFunc

universe u

/-- A rational function field is essentially of finite type over its coefficient field. -/
instance instEssFiniteType (k : Type u) [Field k] :
    Algebra.EssFiniteType k (RatFunc k) := by
  rw [← IntermediateField.fg_top_iff]
  simpa [Finset.coe_singleton, RatFunc.adjoin_X] using
    (IntermediateField.fg_adjoin_finset (F := k)
      ({(RatFunc.X : RatFunc k)} : Finset (RatFunc k)))

/-- A rational function field is not finite-dimensional over its coefficient field. -/
theorem not_finiteDimensional (k : Type u) [Field k] :
    ¬ FiniteDimensional k (RatFunc k) := by
  intro h
  -- Local instance justification (proof-local temporary data): expose the assumed finite-dimensionality to the algebraicity API.
  letI : FiniteDimensional k (RatFunc k) := h
  exact (Algebra.transcendental_iff_not_isAlgebraic.mp RatFunc.transcendental)
    (Algebra.IsAlgebraic.of_finite k (RatFunc k))

end RatFunc
