module

public import stacks_project.Chap52.Proposition_52_12_3
public import ReasLib.RingTheory.Spectrum.Prime.Connected.Adic
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 52.14.2 -/
@[stacks 0EG5] #check
  (PrimeSpectrum.zeroLocus_diff_empty_or_connected_of_isAdicComplete :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
      (I a : Ideal A) (hIa : I ≤ a)
      (h_dualizing : CategoryTheory.DerivedCategory.HasCanonicalDualizingComplex A)
      [IsAdicComplete I A]
    (h_dimension : ∀ p q : PrimeSpectrum A,
      p.asIdeal ∈ minimalPrimes A →
        p ∉ PrimeSpectrum.zeroLocus (I : Set A) →
          q ∈ PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩
            PrimeSpectrum.zeroLocus (a : Set A) →
              ((Ideal.LocalCohomology.dimension I
                  I.fg_of_isNoetherianRing + 1 : ℤ) : EInt) <
                WithBot.map (WithTop.map Int.ofNat)
                  (ringKrullDim (p.asIdeal.quotientAtPrime q)))
    (h_connectedNeighborhoods : ∀ V : Set (PrimeSpectrum A),
      IsOpen V → V.Nonempty →
        PrimeSpectrum.zeroLocus (I : Set A) \
            PrimeSpectrum.zeroLocus (a : Set A) ⊆ V →
          _root_.IsConnected V),
    PrimeSpectrum.zeroLocus (I : Set A) \
          PrimeSpectrum.zeroLocus (a : Set A) = ∅ ∨
      _root_.IsConnected
        (PrimeSpectrum.zeroLocus (I : Set A) \
          PrimeSpectrum.zeroLocus (a : Set A)))
