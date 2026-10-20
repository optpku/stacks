module

public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Normalized.DualizingModule
public import ReasLib.RingTheory.Ideal.MinimalPrime.TopDimension

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.IsNormalizedDualizingComplex

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
variable [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
variable (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
variable (ω : DerivedCategory (ModuleCat.{u} A)) (hω : ω.IsNormalizedDualizingComplex H)

/-- The support of the dualizing module is the union of the zero loci of the
top-dimensional minimal primes of a Noetherian local ring. -/
theorem support_dualizingModule :
    Module.support A (dualizingModule H ω hω) =
      ⋃ p ∈ minimalPrimes.topDim A, PrimeSpectrum.zeroLocus p := sorry

end CategoryTheory.DerivedCategory.IsNormalizedDualizingComplex

end
