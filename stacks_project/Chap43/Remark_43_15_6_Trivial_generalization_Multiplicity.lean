/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Ideal.HilbertSamuel.Annihilator
public import ReasLib.RingTheory.Ideal.HilbertSamuel.Asymptotic

@[expose] public section

universe u v

namespace Ideal.HilbertSamuel

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

/- Compatibility surface for degree-indexed multiplicity invariance. -/
#check
  (Ideal.HilbertSamuel.multiplicityInDegree_add_annihilator :
    ∀ (I : Ideal R) (d : ℕ),
      (I + Module.annihilator R M).IsIdealOfDefinition →
        multiplicityInDegree I M d =
          multiplicityInDegree (I + Module.annihilator R M) M d)

/- Compatibility surface for the lower-degree Hilbert--Samuel polynomial decomposition. -/
#check
  (Ideal.HilbertSamuel.chiPolynomial_eq_multiplicity_add_lowerDegree :
    ∀ (I : Ideal R) (d : ℕ),
      (I + Module.annihilator R M).IsIdealOfDefinition →
      Module.supportDim R M ≤ d →
      ∃ Q : Polynomial ℚ,
        Q.degree < d ∧
          chiPolynomial I M =
            Polynomial.monomial d
              (multiplicityInDegree I M d / (d.factorial : ℚ)) + Q)

end Ideal.HilbertSamuel
