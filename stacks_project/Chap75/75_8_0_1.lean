/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent.Closure
import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Comparison
import stacks_project.Chap66.Definition_66_24_1_Noetherian
import stacks_project.Chap66.Definition_66_29_1_RingedSite
import stacks_project.Chap66.Lemma_66_29_7_Quasicoherent
import stacks_project.Chap69.Definition_69_12_1_Instances
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.AlgebraicSpace

universe u w

variable {S : Scheme.{u}} (X : AlgebraicSpace S) [IsLocallyNoetherian X]
variable [ObjectProperty.IsWeakSerreClass
  (SheafOfModules.isCoherent (structureSheaf X))]
variable [HasDerivedCategory.{w} (SheafOfModules (structureSheaf X))]
variable [HasDerivedCategory.{w}
  (SheafOfModules.isCoherent (structureSheaf X)).FullSubcategory]

/- 75.8.0.1: the canonical functor `D(Coh(𝒪_X)) ⥤ D_Coh(𝒪_X)` from the derived
category of coherent modules on a locally Noetherian algebraic space `X` over `S`
to the full subcategory of complexes with coherent cohomology. -/
@[stacks 08GJ] #check
  (CategoryTheory.DerivedCategory.CohomologyIn.Comparison.functor
      (SheafOfModules.isCoherent (structureSheaf X)) :
    DerivedCategory (SheafOfModules.isCoherent (structureSheaf X)).FullSubcategory ⥤
      DerivedCategory.CohomologyIn (SheafOfModules.isCoherent (structureSheaf X)))
