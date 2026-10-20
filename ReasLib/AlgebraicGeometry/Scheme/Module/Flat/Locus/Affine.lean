module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.Locus.WeaklyAssociated
public import ReasLib.AlgebraicGeometry.Scheme.Module.WeaklyAssociatedPoints.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Module.Tilde.BasicOpen
public import ReasLib.RingTheory.Flat.Locus

/-!
# Flat loci for finite modules over affine schemes

For a finite module over a finitely presented algebra, finiteness of the weakly associated
primes of the base ring makes the relative flatness locus open. On each principal open in this
locus, the localized module is finitely presented over the localized target and flat over the
original base.
-/

@[expose] public section

universe u v w

namespace Module.FlatLocus

/-- For a finite module over a finitely presented algebra, the locus where its prime
localizations are flat over the base is open when the base ring has finitely many weakly
associated primes. -/
@[stacks 05IL]
theorem isOpen_of_finite_weakAss
    (R : Type u) (S : Type v) (M : Type w)
    [CommRing R] [CommRing S] [Algebra R S] [Algebra.FinitePresentation R S]
    [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
    [Module.Finite S M] (h_weakAss : (weaklyAssociatedPrimes R R).Finite) :
    IsOpen (Module.flatOverBaseLocus R S M) := sorry

/-- If a principal open is contained in the relative flatness locus of a finite module over a
finitely presented algebra, the corresponding away localization is finitely presented over the
localized target ring. -/
@[stacks 05IL]
theorem finitePresentation_away
    (R : Type u) (S : Type v) (M : Type w)
    [CommRing R] [CommRing S] [Algebra R S] [Algebra.FinitePresentation R S]
    [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
    [Module.Finite S M] (h_weakAss : (weaklyAssociatedPrimes R R).Finite)
    (g : S)
    (h_g : (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum S)) ⊆
      Module.flatOverBaseLocus R S M) :
    Module.FinitePresentation (Localization.Away g) (LocalizedModule.Away g M) := sorry

/-- If a principal open is contained in the relative flatness locus of a finite module over a
finitely presented algebra, the corresponding away localization is flat over the original base
ring. -/
@[stacks 05IL]
theorem flat_away
    (R : Type u) (S : Type v) (M : Type w)
    [CommRing R] [CommRing S] [Algebra R S] [Algebra.FinitePresentation R S]
    [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
    [Module.Finite S M] (h_weakAss : (weaklyAssociatedPrimes R R).Finite)
    (g : S)
    (h_g : (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum S)) ⊆
      Module.flatOverBaseLocus R S M) :
    Module.Flat R (LocalizedModule.Away g M) := sorry

end Module.FlatLocus
