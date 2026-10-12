/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.IdealPower.DerivedTorsion

open CategoryTheory

noncomputable section

universe u

variable {A : Type u} [CommRing A] (I : Ideal A)

#check (CategoryTheory.ModuleCat.IdealPowerTorsion.derivedAdjunction I :
  CategoryTheory.ModuleCat.IdealPowerTorsion.derivedInclusion I ⊣
    CategoryTheory.ModuleCat.IdealPowerTorsion.derivedTorsion I)
