module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Tactic.CrossRefAttribute

/-!
# Closed images of localization spectra

This leaf records the algebraic consequences of the image of a localization
spectrum being closed in the source spectrum.

@stack 02JH
-/

@[expose] public section

noncomputable section

universe u

namespace Localization

variable {R : Type u} [CommRing R]

/-- If the image of the spectrum of a localization is closed, then the
canonical localization map is surjective. -/
@[stacks 02JH "surjective localization map"]
theorem algebraMap_surjective_of_isClosed_range_comap (S : Submonoid R)
    (hclosed : IsClosed
      (Set.range (PrimeSpectrum.comap (algebraMap R (Localization S))))) :
    Function.Surjective (algebraMap R (Localization S)) := sorry

/-- Lemma 10.33.1: a localization whose image on prime spectra is closed is
isomorphic to a quotient of the original ring. -/
@[stacks 02JH "quotient presentation"]
theorem exists_ideal_ringEquiv_quotient_of_isClosed_range_comap
    (S : Submonoid R)
    (hclosed : IsClosed
      (Set.range (PrimeSpectrum.comap (algebraMap R (Localization S))))) :
    ∃ I : Ideal R, Nonempty (Localization S ≃+* R ⧸ I) := sorry

end Localization
