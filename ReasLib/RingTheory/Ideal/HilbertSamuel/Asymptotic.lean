/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Ideal.HilbertSamuel.Annihilator

@[expose] public section

universe u v

namespace Ideal.HilbertSamuel

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- When `I` has finite colength on `M`, its Hilbert--Samuel polynomial is its degree-`d`
multiplicity term plus a polynomial of degree strictly below `d`, whenever the support
dimension is at most `d`. -/
theorem chiPolynomial_eq_multiplicity_add_lowerDegree (I : Ideal R) (d : ℕ)
    (hI : (I + Module.annihilator R M).IsIdealOfDefinition)
    (hd : Module.supportDim R M ≤ d) :
    ∃ Q : Polynomial ℚ,
      Q.degree < d ∧
        chiPolynomial I M =
          Polynomial.monomial d
            (multiplicityInDegree I M d / (d.factorial : ℚ)) + Q := sorry

end Ideal.HilbertSamuel
