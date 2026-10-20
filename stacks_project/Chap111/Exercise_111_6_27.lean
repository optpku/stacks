module

public import ReasLib.RingTheory.Spectrum.Prime.Connected.Product
import StacksCheckRecall

@[expose] public section

universe u

/- Exercise 111.6.27: for a nonzero ring `A`, `PrimeSpectrum A` is disconnected if and only if
`A ≃+* B × C` for some nonzero rings `B` and `C`. -/
@[stacks 02DG] #check
  (PrimeSpectrum.not_connectedSpace_iff_exists_ringEquiv_prod :
    ∀ {A : Type u} [CommRing A] [Nontrivial A],
      ¬ ConnectedSpace (PrimeSpectrum A) ↔
        ∃ (B C : Type u) (_ : CommRing B) (_ : CommRing C) (_ : Nontrivial B) (_ : Nontrivial C),
          Nonempty (A ≃+* B × C))

/- Companion: `PrimeSpectrum (R × S)` is homeomorphic to the disjoint union of
`PrimeSpectrum R` and `PrimeSpectrum S`. -/
#check @PrimeSpectrum.primeSpectrumProdHomeo

/- Companion: `PrimeSpectrum R` is nonempty if and only if `R` is nontrivial. -/
#check @PrimeSpectrum.nonempty_iff_nontrivial
