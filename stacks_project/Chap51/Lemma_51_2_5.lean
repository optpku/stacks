/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.PrimeComplement
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory Limits

namespace CategoryTheory.DerivedCategory.LocalCohomology

/- Lemma 51.2.5: for a finitely generated ideal `I`, a prime ideal `p`, an
`A`-module `M`, and `i ≥ 0`, the prime-complement comparison has image equal
to the localization kernel, is monic under lower-degree localized vanishing,
and is an isomorphism when both relevant localized groups vanish. -/
@[stacks 0DWU] #check
  (CategoryTheory.DerivedCategory.LocalCohomology.primeComplementComparison_range :
    {A : Type u} → [CommRing A] → (I p : Ideal A) → [p.IsPrime] → (hI : I.FG) →
      (M : ModuleCat A) → (i : ℤ) → (hi : 0 ≤ i) →
      (RΓI : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I) →
      (RΓ : (f : p.primeCompl.Divisibility) →
        DerivedCategory (ModuleCat A) ⥤
          IdealPowerTorsion (primeComplementSupport I p f)) →
      (hRΓI : IdealPowerTorsion.inclusion I ⊣ RΓI) →
      (hRΓ : ∀ f : p.primeCompl.Divisibility,
        IdealPowerTorsion.inclusion (primeComplementSupport I p f) ⊣ RΓ f) →
      (primeComplementComparison I p hI M i hi RΓI RΓ hRΓI hRΓ).hom.range =
        (LocalizedModule.mkLinearMap p.primeCompl
          (supportedCohomology I RΓI M i)).ker)

#check
  (CategoryTheory.DerivedCategory.LocalCohomology.primeComplementComparison_injective :
    {A : Type u} → [CommRing A] → (I p : Ideal A) → [p.IsPrime] → (hI : I.FG) →
      (M : ModuleCat A) → (i : ℤ) → (hi : 0 ≤ i) →
      (RΓI : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I) →
      (RΓ : (f : p.primeCompl.Divisibility) →
        DerivedCategory (ModuleCat A) ⥤
          IdealPowerTorsion (primeComplementSupport I p f)) →
      (hRΓI : IdealPowerTorsion.inclusion I ⊣ RΓI) →
      (hRΓ : ∀ f : p.primeCompl.Divisibility,
        IdealPowerTorsion.inclusion (primeComplementSupport I p f) ⊣ RΓ f) →
      [Subsingleton (LocalizedModule p.primeCompl
        (supportedCohomology I RΓI M (i - 1)))] →
      Function.Injective (primeComplementComparison I p hI M i hi RΓI RΓ hRΓI hRΓ))

#check
  (CategoryTheory.DerivedCategory.LocalCohomology.primeComplementComparison_bijective :
    {A : Type u} → [CommRing A] → (I p : Ideal A) → [p.IsPrime] → (hI : I.FG) →
      (M : ModuleCat A) → (i : ℤ) → (hi : 0 ≤ i) →
      (RΓI : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I) →
      (RΓ : (f : p.primeCompl.Divisibility) →
        DerivedCategory (ModuleCat A) ⥤
          IdealPowerTorsion (primeComplementSupport I p f)) →
      (hRΓI : IdealPowerTorsion.inclusion I ⊣ RΓI) →
      (hRΓ : ∀ f : p.primeCompl.Divisibility,
        IdealPowerTorsion.inclusion (primeComplementSupport I p f) ⊣ RΓ f) →
      [Subsingleton (LocalizedModule p.primeCompl
        (supportedCohomology I RΓI M (i - 1)))] →
      [Subsingleton (LocalizedModule p.primeCompl
        (supportedCohomology I RΓI M i))] →
      Function.Bijective (primeComplementComparison I p hI M i hi RΓI RΓ hRΓI hRΓ))

end CategoryTheory.DerivedCategory.LocalCohomology
