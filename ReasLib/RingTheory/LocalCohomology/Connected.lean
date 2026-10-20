module

public import Mathlib.Order.WithBotTop
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.Sets.Closeds
public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.CohomologicalDimension
public import ReasLib.RingTheory.Completion.LocalRing

@[expose] public section

noncomputable section

universe u

namespace Ideal.LocalCohomology

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsCompleteLocalRing A]

/-- Let `A` be a Noetherian complete local ring and `I` a proper ideal. If `c` is
the least dimension of a closed subset with disconnected complement and `d` is the
least dimension of an irreducible component, then a closed subset `Z` of `V(I)`
has connected complement in `V(I)` whenever
`dim Z + cd(A, I) + 1 < min (c + 1) d`. -/
theorem zeroLocus_diff_connected_of_dimension_lt
    (I : Ideal A) (hI : I ≠ ⊤) (c d : EInt)
    (h_d : IsLeast
      (Set.range fun W : irreducibleComponents (PrimeSpectrum A) ↦
        WithBot.map (WithTop.map Int.ofNat)
          (topologicalKrullDim (W : Set (PrimeSpectrum A)))) d)
    (h_c : IsLeast
      (Set.image
        (fun W : TopologicalSpace.Closeds (PrimeSpectrum A) ↦
          WithBot.map (WithTop.map Int.ofNat)
            (topologicalKrullDim (W : Set (PrimeSpectrum A))))
        {W : TopologicalSpace.Closeds (PrimeSpectrum A) |
          ¬ _root_.IsConnected (Set.univ \ (W : Set (PrimeSpectrum A)))}) c)
    (Z : TopologicalSpace.Closeds (PrimeSpectrum A))
    (hZI : (Z : Set (PrimeSpectrum A)) ⊆ PrimeSpectrum.zeroLocus (I : Set A))
    (h_dim :
      WithBot.map (WithTop.map Int.ofNat)
          (topologicalKrullDim (Z : Set (PrimeSpectrum A))) +
        (dimension I I.fg_of_isNoetherianRing : EInt) + (1 : EInt) <
          min (c + (1 : EInt)) d) :
    _root_.IsConnected
      (PrimeSpectrum.zeroLocus (I : Set A) \ (Z : Set (PrimeSpectrum A))) := sorry

/-- Let `A` be a Noetherian complete local ring and `I` a proper ideal. If `c` is
the least dimension of a closed subset with disconnected complement and `d` is the
least dimension of an irreducible component, then the punctured spectrum of
`A ⧸ I` is connected whenever `cd(A, I) + 1 < min (c + 1) d`. -/
theorem quotient_nonmaximalPrimes_connected
    (I : Ideal A) (hI : I ≠ ⊤) (c d : EInt)
    (h_d : IsLeast
      (Set.range fun W : irreducibleComponents (PrimeSpectrum A) ↦
        WithBot.map (WithTop.map Int.ofNat)
          (topologicalKrullDim (W : Set (PrimeSpectrum A)))) d)
    (h_c : IsLeast
      (Set.image
        (fun W : TopologicalSpace.Closeds (PrimeSpectrum A) ↦
          WithBot.map (WithTop.map Int.ofNat)
            (topologicalKrullDim (W : Set (PrimeSpectrum A))))
        {W : TopologicalSpace.Closeds (PrimeSpectrum A) |
          ¬ _root_.IsConnected (Set.univ \ (W : Set (PrimeSpectrum A)))}) c)
    (h_dim :
      (dimension I I.fg_of_isNoetherianRing : EInt) + (1 : EInt) <
        min (c + (1 : EInt)) d) :
    _root_.IsConnected {p : PrimeSpectrum (A ⧸ I) | ¬ p.asIdeal.IsMaximal} := sorry

end Ideal.LocalCohomology
