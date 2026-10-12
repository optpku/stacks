/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.NoetherianRestriction
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory Limits

namespace CategoryTheory.DerivedCategory.LocalCohomology

/- Lemma 51.2.6 (1): vanishing in degree `i` at every prime in `V(I) ∖ V(I')`
implies surjectivity of support restriction in degree `i ≥ 0`. -/
@[stacks 0DWV] #check
  (CategoryTheory.DerivedCategory.LocalCohomology.cohomologyMapOfLE_surjective :
    {A : Type u} → [CommRing A] → [IsNoetherianRing A] →
      (I I' : Ideal A) → (hII' : I ≤ I') → (hI : I.FG) → (hI' : I'.FG) →
      (M : ModuleCat A) → (i : ℤ) → (hi : 0 ≤ i) →
      (RΓI : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I) →
      (RΓI' : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I') →
      (hRΓI : IdealPowerTorsion.inclusion I ⊣ RΓI) →
      (hRΓI' : IdealPowerTorsion.inclusion I' ⊣ RΓI') →
      (∀ p ∈ PrimeSpectrum.zeroLocus I \ PrimeSpectrum.zeroLocus I',
        vanishesAtPrime M i p) →
      Function.Surjective (cohomologyMapOfLE hII' RΓI RΓI' hRΓI hRΓI' M i))

/- Lemma 51.2.6 (2): vanishing in degree `i - 1` at every prime in `V(I) ∖ V(I')`
implies injectivity of support restriction in degree `i ≥ 0`. -/
@[stacks 0DWV] #check
  (CategoryTheory.DerivedCategory.LocalCohomology.cohomologyMapOfLE_injective :
    {A : Type u} → [CommRing A] → [IsNoetherianRing A] →
      (I I' : Ideal A) → (hII' : I ≤ I') → (hI : I.FG) → (hI' : I'.FG) →
      (M : ModuleCat A) → (i : ℤ) → (hi : 0 ≤ i) →
      (RΓI : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I) →
      (RΓI' : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I') →
      (hRΓI : IdealPowerTorsion.inclusion I ⊣ RΓI) →
      (hRΓI' : IdealPowerTorsion.inclusion I' ⊣ RΓI') →
      (∀ p ∈ PrimeSpectrum.zeroLocus I \ PrimeSpectrum.zeroLocus I',
        vanishesAtPrime M (i - 1) p) →
      Function.Injective (cohomologyMapOfLE hII' RΓI RΓI' hRΓI hRΓI' M i))

/- Lemma 51.2.6 (3): vanishing in degrees `i` and `i - 1` at every prime in
`V(I) ∖ V(I')` implies bijectivity of support restriction in degree `i ≥ 0`. -/
@[stacks 0DWV] #check
  (CategoryTheory.DerivedCategory.LocalCohomology.cohomologyMapOfLE_bijective :
    {A : Type u} → [CommRing A] → [IsNoetherianRing A] →
      (I I' : Ideal A) → (hII' : I ≤ I') → (hI : I.FG) → (hI' : I'.FG) →
      (M : ModuleCat A) → (i : ℤ) → (hi : 0 ≤ i) →
      (RΓI : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I) →
      (RΓI' : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I') →
      (hRΓI : IdealPowerTorsion.inclusion I ⊣ RΓI) →
      (hRΓI' : IdealPowerTorsion.inclusion I' ⊣ RΓI') →
      (∀ p ∈ PrimeSpectrum.zeroLocus I \ PrimeSpectrum.zeroLocus I',
        vanishesAtPrime M i p) →
      (∀ p ∈ PrimeSpectrum.zeroLocus I \ PrimeSpectrum.zeroLocus I',
        vanishesAtPrime M (i - 1) p) →
      Function.Bijective (cohomologyMapOfLE hII' RΓI RΓI' hRΓI hRΓI' M i))

end CategoryTheory.DerivedCategory.LocalCohomology
