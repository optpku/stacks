module

import ReasLib.Algebra.Module.IdealPower.Serre
import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Comparison
import StacksCheckRecall

open CategoryTheory

universe u v w

variable {A : Type u} [CommRing A]
variable (I : Ideal A)
variable [HasDerivedCategory.{w} (ModuleCat.{v} A)]
variable [HasDerivedCategory.{w}
  ((ModuleCat.isIdealPowerTorsion I : ObjectProperty (ModuleCat.{v} A)).FullSubcategory)]

/- 47.8.3.1: the canonical functor
`D(I^∞-torsion) ⥤ D_{I^∞-torsion}(A)`. -/
@[stacks 0A6N] #check
  (CategoryTheory.DerivedCategory.CohomologyIn.Comparison.functor
      (ModuleCat.isIdealPowerTorsion I : ObjectProperty (ModuleCat.{v} A)) :
    DerivedCategory
        (ModuleCat.isIdealPowerTorsion I : ObjectProperty (ModuleCat.{v} A)).FullSubcategory ⥤
      DerivedCategory.CohomologyIn
        (ModuleCat.isIdealPowerTorsion I : ObjectProperty (ModuleCat.{v} A)))
