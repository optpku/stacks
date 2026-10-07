module

public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.CohomologicalDimension.KrullDimension
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.IdealComplement
public import ReasLib.RingTheory.Ideal.MinimalPrime.TopDimension

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.DerivedCategory
open CategoryTheory.DerivedCategory.LocalCohomology

universe u

namespace Ideal.LocalCohomology

/-- If a finite module contains every top-dimensional irreducible component in its support
and its degree-d local cohomology with support in an ideal vanishes, then the
local-cohomological dimension of that ideal is strictly less than d. -/
theorem dimension_lt_of_topCohomology_isZero {A M : Type u} [CommRing A]
    [IsNoetherianRing A] [AddCommGroup M] [Module A M] [Module.Finite A M]
    (I : Ideal A) (d : ℕ) (hdim : ringKrullDim A = d)
    (RΓ : DerivedCategory (ModuleCat A) ⥤ DerivedCategory.IdealPowerTorsion I)
    (hRΓ : DerivedCategory.IdealPowerTorsion.inclusion I ⊣ RΓ)
    (h_support : ∀ p ∈ minimalPrimes.topDim A,
      PrimeSpectrum.zeroLocus p ⊆ Module.support A M)
    (h_vanish : IsZero (supportedCohomology I RΓ (ModuleCat.of A M) (d : ℤ))) :
    dimension I I.fg_of_isNoetherianRing < (d : ℤ) := sorry

end Ideal.LocalCohomology
