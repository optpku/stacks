/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.Depth

universe u

open CategoryTheory CategoryTheory.Limits

#check (Ideal.derivedDepth :
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (RΓ : DerivedCategory (ModuleCat.{u} A) ⥤
      DerivedCategory.IdealPowerTorsion I)
    (hRΓ : DerivedCategory.IdealPowerTorsion.inclusion I ⊣ RΓ)
    (K : DerivedCategory.Plus.CohomologyIn
      (ModuleCat.isFinitePresentation A)), WithTop ℤ)

#check (Ideal.derivedDepth_eq_sSup :
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (RΓ : DerivedCategory (ModuleCat.{u} A) ⥤
      DerivedCategory.IdealPowerTorsion I)
    (hRΓ : DerivedCategory.IdealPowerTorsion.inclusion I ⊣ RΓ)
    (K : DerivedCategory.Plus.CohomologyIn
      (ModuleCat.isFinitePresentation A)),
    I.derivedDepth RΓ hRΓ K =
      sSup {m : WithTop ℤ | ∀ i : ℤ, (i : WithTop ℤ) < m →
        IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
          (RΓ.obj ((DerivedCategory.Plus.CohomologyIn.ambient
            (ModuleCat.isFinitePresentation A)).obj K)).obj)})

#check (CategoryTheory.DerivedCategory.depth :
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (RΓ : DerivedCategory (ModuleCat.{u} A) ⥤
      DerivedCategory.IdealPowerTorsion (IsLocalRing.maximalIdeal A))
    (hRΓ : DerivedCategory.IdealPowerTorsion.inclusion
      (IsLocalRing.maximalIdeal A) ⊣ RΓ)
    (K : DerivedCategory.Plus.CohomologyIn
      (ModuleCat.isFinitePresentation A)), WithTop ℤ)

#check (CategoryTheory.DerivedCategory.depth_eq_maximalIdeal_derivedDepth :
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (RΓ : DerivedCategory (ModuleCat.{u} A) ⥤
      DerivedCategory.IdealPowerTorsion (IsLocalRing.maximalIdeal A))
    (hRΓ : DerivedCategory.IdealPowerTorsion.inclusion
      (IsLocalRing.maximalIdeal A) ⊣ RΓ)
    (K : DerivedCategory.Plus.CohomologyIn
      (ModuleCat.isFinitePresentation A)),
    CategoryTheory.DerivedCategory.depth RΓ hRΓ K =
      (IsLocalRing.maximalIdeal A).derivedDepth RΓ hRΓ K)
