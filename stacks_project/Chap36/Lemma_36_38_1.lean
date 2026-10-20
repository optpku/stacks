/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent
import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent.Closure
import ReasLib.CategoryTheory.DerivedCategory.Bounded.K0
import ReasLib.CategoryTheory.DerivedCategory.Bounded.CohomologyIn.K0
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory

universe u w

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) [IsNoetherian X]
variable [HasDerivedCategory.{w} (SheafOfModules X.ringCatSheaf)]
variable [HasDerivedCategory.{w}
  (SheafOfModules.isCoherent X.ringCatSheaf).FullSubcategory]

/- Lemma 36.38.1 (1): the Grothendieck group of coherent `O_X`-modules is canonically
additively equivalent to that of their bounded derived category. -/
@[stacks 0FDF] #check
  (CategoryTheory.DerivedCategory.Bounded.K0.equiv
      (SheafOfModules.isCoherent X.ringCatSheaf).FullSubcategory :
    CategoryTheory.AbelianK0
        (SheafOfModules.isCoherent X.ringCatSheaf).FullSubcategory ≃+
      CategoryTheory.TriangulatedK0
        (DerivedCategory.Bounded
          (SheafOfModules.isCoherent X.ringCatSheaf).FullSubcategory))

/- Lemma 36.38.1 (2): the Grothendieck group of the bounded derived category of coherent
`O_X`-modules is canonically additively equivalent to that of bounded derived `O_X`-modules
with coherent cohomology. -/
@[stacks 0FDF] #check
  (CategoryTheory.DerivedCategory.Bounded.CohomologyIn.K0.comparisonEquiv
      (SheafOfModules.isCoherent X.ringCatSheaf) :
    CategoryTheory.TriangulatedK0
        (DerivedCategory.Bounded
          (SheafOfModules.isCoherent X.ringCatSheaf).FullSubcategory) ≃+
      CategoryTheory.TriangulatedK0
        (DerivedCategory.Bounded.CohomologyIn
          (SheafOfModules.isCoherent X.ringCatSheaf)))

end AlgebraicGeometry.Scheme
