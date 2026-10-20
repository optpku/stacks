module

import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent
import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent.Closure
import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Comparison
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory

universe u w

variable (X : Scheme.{u}) [IsLocallyNoetherian X]
variable [HasDerivedCategory.{w} (SheafOfModules X.ringCatSheaf)]
variable [HasDerivedCategory.{w}
  (SheafOfModules.isCoherent X.ringCatSheaf).FullSubcategory]

/- 36.11.0.1: the canonical functor from the derived category of coherent
modules on `X` to the full subcategory of complexes with coherent cohomology. -/
@[stacks 08E1] #check
  (CategoryTheory.DerivedCategory.CohomologyIn.Comparison.functor
      (SheafOfModules.isCoherent X.ringCatSheaf) :
    DerivedCategory (SheafOfModules.isCoherent X.ringCatSheaf).FullSubcategory ⥤
      DerivedCategory.CohomologyIn (SheafOfModules.isCoherent X.ringCatSheaf))
