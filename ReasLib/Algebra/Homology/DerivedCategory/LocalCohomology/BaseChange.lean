/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.Cech
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.IdealPower.ScalarExtension
public import ReasLib.CategoryTheory.Adjunction.BaseChange

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.LocalCohomology.BaseChange

open ModuleCat.IdealPower.DerivedBaseChange

variable {A B : Type u} [CommRing A] [CommRing B]

/-- The canonical local-cohomology base-change transformation, obtained as the right mate
of the inclusion comparison for restricted derived extension of scalars. -/
noncomputable def comparison (f : A →+* B) (I : Ideal A) (hI : I.FG)
    (RΓA : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I)
    (RΓB : DerivedCategory (ModuleCat B) ⥤ IdealPowerTorsion (I.map f))
    (hA : IdealPowerTorsion.inclusion I ⊣ RΓA)
    (hB : IdealPowerTorsion.inclusion (I.map f) ⊣ RΓB) :
    RΓA ⋙ extensionOfFG f I hI ⟶
      ModuleCat.derivedExtensionOfScalars f ⋙ RΓB :=
  CategoryTheory.DerivedBaseChange.map hA hB (extensionOfFGCompιIso f I hI)

/-- The transformation `comparison` is characterized by the canonical adjunction-mate
equation for the inclusion comparison. -/
theorem comparison_spec (f : A →+* B) (I : Ideal A) (hI : I.FG)
    (RΓA : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I)
    (RΓB : DerivedCategory (ModuleCat B) ⥤ IdealPowerTorsion (I.map f))
    (hA : IdealPowerTorsion.inclusion I ⊣ RΓA)
    (hB : IdealPowerTorsion.inclusion (I.map f) ⊣ RΓB) :
    CategoryTheory.DerivedBaseChange.IsMap hA hB
      (extensionOfFGCompιIso f I hI) (comparison f I hI RΓA RΓB hA hB) := sorry

end CategoryTheory.DerivedCategory.LocalCohomology.BaseChange

namespace CategoryTheory.DerivedCategory.LocalCohomology

open BaseChange

variable {A B : Type u} [CommRing A] [CommRing B]

/-- The canonical local-cohomology base-change transformation for a finitely generated
ideal is an isomorphism. -/
noncomputable instance comparisonIsIso (f : A →+* B) (I : Ideal A) (hI : I.FG)
    (RΓA : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I)
    (RΓB : DerivedCategory (ModuleCat B) ⥤ IdealPowerTorsion (I.map f))
    (hA : IdealPowerTorsion.inclusion I ⊣ RΓA)
    (hB : IdealPowerTorsion.inclusion (I.map f) ⊣ RΓB) :
    IsIso (comparison f I hI RΓA RΓB hA hB) := sorry

end CategoryTheory.DerivedCategory.LocalCohomology
