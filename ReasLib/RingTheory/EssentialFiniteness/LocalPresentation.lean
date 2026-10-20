module

public import ReasLib.RingTheory.EssentialFiniteness.Basic
public import ReasLib.RingTheory.Spectrum.Maximal.Over
import Mathlib.Tactic.CrossRefAttribute

/-!
# Local presentations of essentially finite type maps

This leaf records polynomial-quotient presentations after localization at a
maximal ideal over the closed point of the base local ring.

@stack 0AUG
-/

@[expose] public section

universe u v

open IsLocalRing

namespace RingHom.EssFiniteType

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]

/-- Lemma 10.54.5: an essentially finite type map between local rings admits a
presentation as a localization of a quotient of a local polynomial ring. The
map need not be local. -/
@[stacks 0AUG]
theorem exists_localizedPolynomialQuotient
    (φ : R →+* S) (hφ : φ.EssFiniteType) :
    ∃ (n : ℕ)
      (m : MaximalSpectrum.over (maximalIdeal R) (MvPolynomial (Fin n) R))
      (ψ : Localization.AtPrime m.1.asIdeal →+* S),
        ψ.IsLocalizationOfQuotient ∧
          φ = ψ.comp (algebraMap R (Localization.AtPrime m.1.asIdeal)) := sorry

end RingHom.EssFiniteType
