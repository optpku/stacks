/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.Completion
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits DerivedCategory
open SequentialInverseSystem.Milnor.ProductCone

noncomputable section

universe u

/- Lemma 47.12.4: derived completion of local cohomology is the homotopy limit
of local cohomology of the positive ideal-power quotient tower. -/
@[stacks 0EEW] #check
  (CategoryTheory.DerivedCategory.LocalCohomology.Completion.isHomotopyLimit :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] (I J : Ideal A)
      (M : ModuleCat.{u} A) [Module.Finite A M]
      (RΓZ : DerivedCategory (ModuleCat.{u} A) ⥤
        CategoryTheory.DerivedCategory.IdealPowerTorsion J),
      (CategoryTheory.DerivedCategory.IdealPowerTorsion.inclusion J ⊣ RΓZ) →
        HomotopyLimit.IsOf
          (CategoryTheory.DerivedCategory.LocalCohomology.Completion.quotientSystem
            I J RΓZ M)
          (derivedCompletionOf I I.fg_of_isNoetherianRing
            (RΓZ.obj (ModuleCat.single0 M)).obj))

#check
  (CategoryTheory.DerivedCategory.LocalCohomology.Completion.cohomologyShortExact :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] (I J : Ideal A)
      (M : ModuleCat.{u} A) [Module.Finite A M]
      (RΓZ : DerivedCategory (ModuleCat.{u} A) ⥤
        CategoryTheory.DerivedCategory.IdealPowerTorsion J)
      (_ : CategoryTheory.DerivedCategory.IdealPowerTorsion.inclusion J ⊣ RΓZ) (i : ℤ),
      ∃ (ι : canonicalR1
            (CategoryTheory.DerivedCategory.LocalCohomology.Completion.quotientSystem
                I J RΓZ M ⋙ homologyFunctor (ModuleCat.{u} A) (i - 1)) ⟶
            (homologyFunctor (ModuleCat.{u} A) i).obj
              (derivedCompletionOf I I.fg_of_isNoetherianRing
                (RΓZ.obj (ModuleCat.single0 M)).obj))
        (π : (homologyFunctor (ModuleCat.{u} A) i).obj
              (derivedCompletionOf I I.fg_of_isNoetherianRing
                (RΓZ.obj (ModuleCat.single0 M)).obj) ⟶
            limit
              (CategoryTheory.DerivedCategory.LocalCohomology.Completion.quotientSystem
                I J RΓZ M ⋙ homologyFunctor (ModuleCat.{u} A) i))
        (h : ι ≫ π = 0),
        (ShortComplex.mk ι π h).ShortExact)

#check
  (CategoryTheory.DerivedCategory.LocalCohomology.Completion.isGE_zero :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] (I J : Ideal A)
      (M : ModuleCat.{u} A) [Module.Finite A M]
      (RΓZ : DerivedCategory (ModuleCat.{u} A) ⥤
        CategoryTheory.DerivedCategory.IdealPowerTorsion J),
      (CategoryTheory.DerivedCategory.IdealPowerTorsion.inclusion J ⊣ RΓZ) →
        (derivedCompletionOf I I.fg_of_isNoetherianRing
          (RΓZ.obj (ModuleCat.single0 M)).obj).IsGE 0)

#check
  (CategoryTheory.DerivedCategory.LocalCohomology.Completion.homology_isZero_of_neg :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] (I J : Ideal A)
      (M : ModuleCat.{u} A) [Module.Finite A M]
      (RΓZ : DerivedCategory (ModuleCat.{u} A) ⥤
        CategoryTheory.DerivedCategory.IdealPowerTorsion J)
      (_ : CategoryTheory.DerivedCategory.IdealPowerTorsion.inclusion J ⊣ RΓZ)
      (i : ℤ), i < 0 →
        IsZero ((homologyFunctor (ModuleCat.{u} A) i).obj
          (derivedCompletionOf I I.fg_of_isNoetherianRing
            (RΓZ.obj (ModuleCat.single0 M)).obj)))
