/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DiscreteValuationRing.Localization.ReducedQuotient
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.UniformizerRoot
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.FieldRamification

@[expose] public section

universe u

noncomputable section

namespace DVR.UniformizerRoot

/-- At a minimal prime over a nonzerodivisor with reduced principal quotient in a
Noetherian ring, adjoining a positive root of its image in the local fraction field is
tamely ramified whenever the exponent is a unit in the original ring. -/
theorem isTamelyRamified_atMinimalPrime
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (f : A) (hf : f ∈ nonZeroDivisors A) [IsReduced (A ⧸ Ideal.span {f})]
    (e : ℕ) (he : 1 ≤ e) (he_unit : IsUnit (e : A))
    (p : Ideal A) [p.IsPrime] (hp : p ∈ (Ideal.span {f}).minimalPrimes) :
    let h_local := minimalPrimes.isDiscreteValuationRing_atPrime_of_reduced_quotient f hf p hp
    -- Local instance justification (defeq pin): the minimal-prime localization theorem supplies the domain proof indexing the derived local DVR structure.
    letI : IsDomain (Localization.AtPrime p) := h_local.choose
    -- Local instance justification (proof-local temporary data): the nonzerodivisor and minimal-prime hypotheses derive the DVR structure at this localization.
    letI : IsDiscreteValuationRing (Localization.AtPrime p) := h_local.choose_spec.1
    -- Local instance justification (proof-local temporary data): locally derived irreducibility supplies the canonical root-extension field API.
    letI : Fact (Irreducible (fractionPolynomial (algebraMap A (Localization.AtPrime p) f) e)) :=
      ⟨fractionPolynomial_irreducible
        ((IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr h_local.choose_spec.2)
        (Nat.ne_zero_of_lt he)⟩
    @DVR.Field.IsTamelyRamified
      (Localization.AtPrime p) (FractionRing (Localization.AtPrime p))
      (RootExtension (algebraMap A (Localization.AtPrime p) f) e)
      _ _ _ _ _ _ _ baseAlgebra fractionAlgebra
      (IsScalarTower.of_algebraMap_eq' rfl) := sorry

end DVR.UniformizerRoot
