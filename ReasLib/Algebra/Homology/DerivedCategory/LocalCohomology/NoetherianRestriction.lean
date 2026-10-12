/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.LocalCohomology
public import Mathlib.Algebra.Module.LocalizedModule.AtPrime
public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.SupportRestriction

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace CategoryTheory.DerivedCategory.LocalCohomology

variable {A : Type u} [CommRing A]

/-- Vanishing in integer degree `n` of the local cohomology of `M` localized at `p`,
supported at the maximal ideal of the localized ring; negative degrees vanish by convention. -/
def vanishesAtPrime (M : ModuleCat A) (n : ℤ) (p : PrimeSpectrum A) : Prop :=
  0 ≤ n →
    IsZero ((localCohomology
      (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal)) n.toNat).obj
        (ModuleCat.of (Localization.AtPrime p.asIdeal)
          (LocalizedModule.AtPrime p.asIdeal M)))

/-- In a nonnegative degree, vanishing at a prime is precisely vanishing of the
canonical local-cohomology module over the localized ring. -/
theorem vanishesAtPrime_iff_of_nonneg (M : ModuleCat A) (n : ℤ)
    (p : PrimeSpectrum A) (hn : 0 ≤ n) :
    vanishesAtPrime M n p ↔
      IsZero ((localCohomology
        (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal)) n.toNat).obj
          (ModuleCat.of (Localization.AtPrime p.asIdeal)
            (LocalizedModule.AtPrime p.asIdeal M))) := sorry

/-- Local cohomology at a prime vanishes in negative integer degrees. -/
theorem vanishesAtPrime_of_neg (M : ModuleCat A) (n : ℤ)
    (p : PrimeSpectrum A) (hn : n < 0) :
    vanishesAtPrime M n p := sorry

/-- The degreewise map on supported cohomology induced by restriction along `I ≤ I'`. -/
noncomputable def cohomologyMapOfLE {I I' : Ideal A} (hII' : I ≤ I')
    (RΓI : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I)
    (RΓI' : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I')
    (hRΓI : IdealPowerTorsion.inclusion I ⊣ RΓI)
    (hRΓI' : IdealPowerTorsion.inclusion I' ⊣ RΓI')
    (M : ModuleCat A) (i : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat A) i).obj ((RΓI'.obj (ModuleCat.single0 M)).obj) ⟶
      (DerivedCategory.homologyFunctor (ModuleCat A) i).obj ((RΓI.obj (ModuleCat.single0 M)).obj) :=
  (DerivedCategory.homologyFunctor (ModuleCat A) i).map
    (supportRestrictionAmbientApp hII' RΓI RΓI' hRΓI hRΓI'
      (ModuleCat.single0 M))

/-- The cohomology map of an ideal inclusion factors the `I'`-supported counit through
the `I`-supported counit in degree `i`. -/
theorem cohomologyMapOfLE_fac {I I' : Ideal A} (hII' : I ≤ I')
    (RΓI : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I)
    (RΓI' : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I')
    (hRΓI : IdealPowerTorsion.inclusion I ⊣ RΓI)
    (hRΓI' : IdealPowerTorsion.inclusion I' ⊣ RΓI')
    (M : ModuleCat A) (i : ℤ) :
    cohomologyMapOfLE hII' RΓI RΓI' hRΓI hRΓI' M i ≫
        (DerivedCategory.homologyFunctor (ModuleCat A) i).map
          (hRΓI.counit.app (ModuleCat.single0 M)) =
      (DerivedCategory.homologyFunctor (ModuleCat A) i).map
        (hRΓI'.counit.app (ModuleCat.single0 M)) := sorry

/-- Over a Noetherian ring, support restriction is surjective in degree `i ≥ 0`
if local cohomology in degree `i` vanishes at every prime in `V(I) ∖ V(I')`. -/
theorem cohomologyMapOfLE_surjective [IsNoetherianRing A]
    (I I' : Ideal A) (hII' : I ≤ I') (hI : I.FG) (hI' : I'.FG)
    (M : ModuleCat A) (i : ℤ) (hi : 0 ≤ i)
    (RΓI : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I)
    (RΓI' : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I')
    (hRΓI : IdealPowerTorsion.inclusion I ⊣ RΓI)
    (hRΓI' : IdealPowerTorsion.inclusion I' ⊣ RΓI')
    (hvan : ∀ p ∈ PrimeSpectrum.zeroLocus I \ PrimeSpectrum.zeroLocus I',
      vanishesAtPrime M i p) :
    Function.Surjective
      (cohomologyMapOfLE hII' RΓI RΓI' hRΓI hRΓI' M i) := sorry

/-- Over a Noetherian ring, support restriction is injective in degree `i ≥ 0`
if local cohomology in degree `i - 1` vanishes at every prime in `V(I) ∖ V(I')`. -/
theorem cohomologyMapOfLE_injective [IsNoetherianRing A]
    (I I' : Ideal A) (hII' : I ≤ I') (hI : I.FG) (hI' : I'.FG)
    (M : ModuleCat A) (i : ℤ) (hi : 0 ≤ i)
    (RΓI : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I)
    (RΓI' : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I')
    (hRΓI : IdealPowerTorsion.inclusion I ⊣ RΓI)
    (hRΓI' : IdealPowerTorsion.inclusion I' ⊣ RΓI')
    (hvan : ∀ p ∈ PrimeSpectrum.zeroLocus I \ PrimeSpectrum.zeroLocus I',
      vanishesAtPrime M (i - 1) p) :
    Function.Injective
      (cohomologyMapOfLE hII' RΓI RΓI' hRΓI hRΓI' M i) := sorry

/-- Over a Noetherian ring, support restriction is bijective in degree `i ≥ 0`
if local cohomology in degrees `i` and `i - 1` vanishes at every prime
in `V(I) ∖ V(I')`. -/
theorem cohomologyMapOfLE_bijective [IsNoetherianRing A]
    (I I' : Ideal A) (hII' : I ≤ I') (hI : I.FG) (hI' : I'.FG)
    (M : ModuleCat A) (i : ℤ) (hi : 0 ≤ i)
    (RΓI : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I)
    (RΓI' : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I')
    (hRΓI : IdealPowerTorsion.inclusion I ⊣ RΓI)
    (hRΓI' : IdealPowerTorsion.inclusion I' ⊣ RΓI')
    (hvan_i : ∀ p ∈ PrimeSpectrum.zeroLocus I \ PrimeSpectrum.zeroLocus I',
      vanishesAtPrime M i p)
    (hvan_pred : ∀ p ∈ PrimeSpectrum.zeroLocus I \ PrimeSpectrum.zeroLocus I',
      vanishesAtPrime M (i - 1) p) :
    Function.Bijective
      (cohomologyMapOfLE hII' RΓI RΓI' hRΓI hRΓI' M i) := sorry

end CategoryTheory.DerivedCategory.LocalCohomology
