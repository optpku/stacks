module

public import ReasLib.RingTheory.Ideal.HilbertSamuel.Dimension
public import ReasLib.RingTheory.Ideal.OfDefinition.ZeroLocus

/-!
# One-dimensional local rings

This leaf exposes the source conditions for dimension one as a reusable Hilbert--Samuel API.  The
dimension and degree owners remain in `Ideal.HilbertSamuel.Dimension`; the source-facing zero-locus,
radical, and ideal-of-definition clauses are kept as direct propositions rather than wrapper
definitions.

@stack 00KK
-/

@[expose] public section

universe u

open Ideal PrimeSpectrum IsLocalRing

namespace Ideal.HilbertSamuel

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- Lemma 10.60.8: for a Noetherian local ring, dimension one, Hilbert--Samuel degree one, the
nonnilpotent closed-point equation, the nonnilpotent radical equation, and the minimal principal
ideal-of-definition criterion are equivalent. -/
@[stacks 00KK]
theorem dimensionOne_tfae :
    List.TFAE
      [ ringKrullDim R = 1
      , degree R R = 1
      , ∃ x : maximalIdeal R,
          ¬ IsNilpotent (x : R) ∧
            zeroLocus ({(x : R)} : Set R) = ({closedPoint R} : Set (PrimeSpectrum R))
      , ∃ x : maximalIdeal R,
          ¬ IsNilpotent (x : R) ∧
            maximalIdeal R = (Ideal.span ({(x : R)} : Set R)).radical
      , (∃ x : Fin 1 → maximalIdeal R,
          (parameterIdeal x).IsIdealOfDefinition) ∧
          ¬ ∃ x : Fin 0 → maximalIdeal R,
            (parameterIdeal x).IsIdealOfDefinition
      ] := sorry

/-- Dimension one is equivalent to a nonnilpotent element whose vanishing locus is the closed
point. -/
@[stacks 00KK "dimension and closed-point zero locus"]
theorem dimensionOne_iff_zeroLocus :
    ringKrullDim R = 1 ↔
      ∃ x : maximalIdeal R,
        ¬ IsNilpotent (x : R) ∧
          zeroLocus ({(x : R)} : Set R) = ({closedPoint R} : Set (PrimeSpectrum R)) := sorry

/-- Dimension one is equivalent to a nonnilpotent element generating an ideal whose radical is the
maximal ideal. -/
@[stacks 00KK "dimension and principal radical"]
theorem dimensionOne_iff_radical :
    ringKrullDim R = 1 ↔
      ∃ x : maximalIdeal R,
        ¬ IsNilpotent (x : R) ∧
          maximalIdeal R = (Ideal.span ({(x : R)} : Set R)).radical := sorry

/-- Dimension one is equivalent to one parameter generating an ideal of definition while no zero
parameter family does. -/
@[stacks 00KK "dimension and minimal parameter ideal of definition"]
theorem dimensionOne_iff_parameterIdeal :
    ringKrullDim R = 1 ↔
      (∃ x : Fin 1 → maximalIdeal R,
          (parameterIdeal x).IsIdealOfDefinition) ∧
        ¬ ∃ x : Fin 0 → maximalIdeal R,
          (parameterIdeal x).IsIdealOfDefinition := sorry

end Ideal.HilbertSamuel

end
