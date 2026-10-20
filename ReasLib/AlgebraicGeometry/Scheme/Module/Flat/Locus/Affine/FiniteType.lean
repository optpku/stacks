module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.Locus.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.Locus.WeaklyAssociated.FiniteType

/-!
# Flat loci for finite modules over finite-type algebras

For a finite module over a finite-type algebra, finiteness of the weakly associated primes of
the base ring makes the relative flatness locus open. On every principal open contained in this
locus, the localized module is flat over the base and finitely presented relative to it.
-/

@[expose] public section

universe u v w

namespace Module.FlatLocus

/-- For a finite module over a finite-type algebra, the locus where its prime localizations are
flat over the base is open when the base ring has finitely many weakly associated primes. -/
@[stacks 05IR]
theorem isOpen_of_finiteType_of_finite_weakAss
    (R : Type u) (S : Type v) (M : Type w)
    [CommRing R] [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
    [Module.Finite S M] (h_weakAss : (weaklyAssociatedPrimes R R).Finite) :
    IsOpen (Module.flatOverBaseLocus R S M) := sorry

/-- If a principal open is contained in the relative flatness locus of a finite module over a
finite-type algebra, the corresponding away localization is flat over the original base ring. -/
@[stacks 05IR]
theorem flat_away_of_finiteType
    (R : Type u) (S : Type v) (M : Type w)
    [CommRing R] [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
    [Module.Finite S M] (h_weakAss : (weaklyAssociatedPrimes R R).Finite)
    (g : S)
    (h_g : (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum S)) ⊆
      Module.flatOverBaseLocus R S M) :
    Module.Flat R (LocalizedModule.Away g M) := sorry

/-- If a principal open is contained in the relative flatness locus of a finite module over a
finite-type algebra, the corresponding away localization is finitely presented relative to the
original base ring. -/
@[stacks 05IR]
theorem finitePresentationRelativeTo_away_of_finiteType
    (R : Type u) (S : Type v) (M : Type w)
    [CommRing R] [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
    [Module.Finite S M] (h_weakAss : (weaklyAssociatedPrimes R R).Finite)
    (g : S)
    (h_g : (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum S)) ⊆
      Module.flatOverBaseLocus R S M) :
    Module.FinitePresentationRelativeTo R (Localization.Away g)
      (LocalizedModule.Away g M) := sorry

end Module.FlatLocus
