module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.Locus.Affine
import StacksCheckRecall

@[expose] public section

universe u v w

/- Lemma 38.13.7 (1): for a finite module over a finitely presented ring map, the locus
where its prime localizations are flat over the base is open when the base ring has only
finitely many weakly associated primes. -/
@[stacks 05IL]
#check
  (Module.FlatLocus.isOpen_of_finite_weakAss :
    ∀ (R : Type u) (S : Type v) (M : Type w)
      [CommRing R] [CommRing S] [Algebra R S] [Algebra.FinitePresentation R S]
      [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
      [Module.Finite S M],
      (weaklyAssociatedPrimes R R).Finite →
        IsOpen (Module.flatOverBaseLocus R S M))

/- Lemma 38.13.7 (2): if a principal open lies in the relative flatness locus, then the
away-localized module is finitely presented over the away-localized target ring. -/
@[stacks 05IL]
#check
  (Module.FlatLocus.finitePresentation_away :
    ∀ (R : Type u) (S : Type v) (M : Type w)
      [CommRing R] [CommRing S] [Algebra R S] [Algebra.FinitePresentation R S]
      [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
      [Module.Finite S M],
      (weaklyAssociatedPrimes R R).Finite →
        ∀ (g : S),
          (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum S)) ⊆
              Module.flatOverBaseLocus R S M →
            Module.FinitePresentation (Localization.Away g) (LocalizedModule.Away g M))

/- Lemma 38.13.7 (3): under the same principal-open hypothesis, the away-localized module
is flat over the original base ring. -/
@[stacks 05IL]
#check
  (Module.FlatLocus.flat_away :
    ∀ (R : Type u) (S : Type v) (M : Type w)
      [CommRing R] [CommRing S] [Algebra R S] [Algebra.FinitePresentation R S]
      [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
      [Module.Finite S M],
      (weaklyAssociatedPrimes R R).Finite →
        ∀ (g : S),
          (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum S)) ⊆
              Module.flatOverBaseLocus R S M →
            Module.Flat R (LocalizedModule.Away g M))
