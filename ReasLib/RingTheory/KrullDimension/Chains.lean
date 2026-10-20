module

public import Mathlib.RingTheory.KrullDimension.Basic

@[expose] public section

universe u

/-- The Krull dimension of a commutative ring is the supremum of lengths of strict chains in
its prime spectrum, with values in `WithBot ℕ∞`. -/
theorem ringKrullDim_eq_iSup_chainLength (R : Type u) [CommRing R] :
    ringKrullDim R = ⨆ chain : LTSeries (PrimeSpectrum R),
      (chain.length : WithBot ℕ∞) := sorry
