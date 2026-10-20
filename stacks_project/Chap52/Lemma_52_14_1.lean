module

public import ReasLib.RingTheory.LocalCohomology.Connected
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 52.14.1: connectedness of closed complements in the zero locus. -/
@[stacks 0ECR] #check (Ideal.LocalCohomology.zeroLocus_diff_connected_of_dimension_lt :
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] [IsCompleteLocalRing A]
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
        (Ideal.LocalCohomology.dimension I I.fg_of_isNoetherianRing : EInt) + (1 : EInt) <
          min (c + (1 : EInt)) d),
    _root_.IsConnected
      (PrimeSpectrum.zeroLocus (I : Set A) \ (Z : Set (PrimeSpectrum A))))

/- Lemma 52.14.1 (2): connectedness of the punctured quotient spectrum. -/
@[stacks 0ECR] #check (Ideal.LocalCohomology.quotient_nonmaximalPrimes_connected :
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] [IsCompleteLocalRing A]
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
      (Ideal.LocalCohomology.dimension I I.fg_of_isNoetherianRing : EInt) + (1 : EInt) <
        min (c + (1 : EInt)) d),
    _root_.IsConnected {p : PrimeSpectrum (A ⧸ I) | ¬ p.asIdeal.IsMaximal})
