/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent
import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Comparison
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory

universe u w

variable (X : Scheme.{u})
variable [HasDerivedCategory.{w} X.Modules]
variable [HasDerivedCategory.{w} (Scheme.QCoh X)]

/- 36.3.0.1: the canonical functor
`D(QCoh(𝒪_X)) ⥤ D_QCoh(𝒪_X)`. -/
@[stacks 06VT] #check
  (CategoryTheory.DerivedCategory.CohomologyIn.Comparison.functor
      (Scheme.quasiCoherentModuleProperty X) :
    DerivedCategory (Scheme.QCoh X) ⥤
      DerivedCategory.CohomologyIn (Scheme.quasiCoherentModuleProperty X))
