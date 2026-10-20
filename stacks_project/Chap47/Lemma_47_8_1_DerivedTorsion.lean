module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.IdealPower.DerivedTorsion

open CategoryTheory

noncomputable section

universe u

variable {A : Type u} [CommRing A] (I : Ideal A)

#check (CategoryTheory.ModuleCat.IdealPowerTorsion.derivedAdjunction I :
  CategoryTheory.ModuleCat.IdealPowerTorsion.derivedInclusion I ⊣
    CategoryTheory.ModuleCat.IdealPowerTorsion.derivedTorsion I)
