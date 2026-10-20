module

public import ReasLib.RingTheory.LocalRing.TameSymbol.Determinant
public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.ScalarQuotient.Determinant.Subtraction

@[expose] public section

universe u v

namespace TameSymbol

/-- The tame symbol of a one-dimensional Noetherian local domain sends `x` and
`1 - x` to one whenever both elements are units in the fraction field. -/
theorem value_one_sub
    (A : Type u) (K : Type v) [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsNoetherianRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    (hdim : ringKrullDim A = 1) (x y : Kˣ) (hy : (y : K) = 1 - (x : K)) :
    value A K hdim x y = 1 := sorry

end TameSymbol
