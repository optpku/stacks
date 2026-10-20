module

public import ReasLib.RingTheory.Etale.Neighborhood.LocalConsequences
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# One etale neighborhood of a closed subset

@stack 07M0

Pointwise etale basic-open neighborhoods of a closed subset can be replaced by one principal
localization whose defining element is a unit modulo the closed-subset ideal.
-/

open PrimeSpectrum
open scoped PrimeSpectrum

universe u v

namespace Algebra

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/-- Lemma 15.9.4: if every point of `V(J)` has an etale basic-open neighborhood, then one element
which is a unit modulo `J` defines an etale away-localization over `A`. -/
@[stacks 07M0]
theorem exists_quotient_unit_and_etale_away_of_zeroLocus
    (J : Ideal B)
    (hJ : ∀ q ∈ PrimeSpectrum.zeroLocus (J : Set B),
      ∃ f : B, q ∈ PrimeSpectrum.basicOpen f ∧ Etale A (Localization.Away f)) :
    ∃ g : B, IsUnit (Ideal.Quotient.mk J g) ∧ Etale A (Localization.Away g) := sorry

/-- For a finitely presented algebra, inclusion of `V(J)` in the canonical etale locus supplies
the pointwise neighborhoods needed by `exists_quotient_unit_and_etale_away_of_zeroLocus`. -/
theorem exists_quotient_unit_and_etale_away_of_zeroLocus_subset_etaleLocus
    [FinitePresentation A B]
    (J : Ideal B) (hJ : PrimeSpectrum.zeroLocus (J : Set B) ⊆ etaleLocus A B) :
    ∃ g : B, IsUnit (Ideal.Quotient.mk J g) ∧ Etale A (Localization.Away g) := sorry

end Algebra
