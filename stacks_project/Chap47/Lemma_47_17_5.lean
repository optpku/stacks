module

public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Normalized.Support
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Normalized.SerreCondition
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.DerivedCategory.IsNormalizedDualizingComplex

noncomputable section

universe u

/- Lemma 47.17.5 (1): the support of the dualizing module is the union of the
top-dimensional irreducible components of `PrimeSpectrum A`. -/
@[stacks 0AWE] #check
  (CategoryTheory.DerivedCategory.IsNormalizedDualizingComplex.support_dualizingModule :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
      (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
      (ω : DerivedCategory (ModuleCat.{u} A))
      (hω : ω.IsNormalizedDualizingComplex H),
      Module.support A (dualizingModule H ω hω) =
        ⋃ p ∈ minimalPrimes.topDim A, PrimeSpectrum.zeroLocus p)

/- Lemma 47.17.5 (2): the dualizing module satisfies Serre's condition `(S₂)`. -/
@[stacks 0AWE] #check
  (CategoryTheory.DerivedCategory.IsNormalizedDualizingComplex.dualizingModuleSerreConditionSTwo :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
      (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
      (ω : DerivedCategory (ModuleCat.{u} A))
      (hω : ω.IsNormalizedDualizingComplex H),
      Module.SerreConditionS A (dualizingModule H ω hω) 2)

end
