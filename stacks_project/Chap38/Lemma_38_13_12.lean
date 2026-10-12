/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.Locus.Affine.FiniteType
import StacksCheckRecall

@[expose] public section

universe u v w

/- Lemma 38.13.12 (1): for a finite module over a finite-type ring map, the locus where its
prime localizations are flat over the base is open when the base ring has only finitely many
weakly associated primes. -/
@[stacks 05IR] #check
  (Module.FlatLocus.isOpen_of_finiteType_of_finite_weakAss :
    ∀ (R : Type u) (S : Type v) (M : Type w)
      [CommRing R] [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
      [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
      [Module.Finite S M] (_ : (weaklyAssociatedPrimes R R).Finite),
      IsOpen (Module.flatOverBaseLocus R S M))

/- Lemma 38.13.12 (2): if a principal open lies in the relative flatness locus, then the
away-localized module is flat over the original base ring. -/
@[stacks 05IR] #check
  (Module.FlatLocus.flat_away_of_finiteType :
    ∀ (R : Type u) (S : Type v) (M : Type w)
      [CommRing R] [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
      [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
      [Module.Finite S M] (_ : (weaklyAssociatedPrimes R R).Finite)
      (g : S) (_ : (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum S)) ⊆
        Module.flatOverBaseLocus R S M),
      Module.Flat R (LocalizedModule.Away g M))

/- Lemma 38.13.12 (3): under the same principal-open hypothesis, the away-localized module
is finitely presented relative to the original base ring. -/
@[stacks 05IR] #check
  (Module.FlatLocus.finitePresentationRelativeTo_away_of_finiteType :
    ∀ (R : Type u) (S : Type v) (M : Type w)
      [CommRing R] [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
      [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
      [Module.Finite S M] (_ : (weaklyAssociatedPrimes R R).Finite)
      (g : S) (_ : (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum S)) ⊆
        Module.flatOverBaseLocus R S M),
      Module.FinitePresentationRelativeTo R (Localization.Away g)
        (LocalizedModule.Away g M))
