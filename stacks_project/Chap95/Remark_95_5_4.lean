/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.QCohStack.CardinalGeneration

open CategoryTheory AlgebraicGeometry
open scoped Cardinal

universe u

variable (κ : Cardinal.{u}) (S : Scheme.{u}) [Fact (ℵ₀ ≤ κ)]

/- Remark 95.5.4: the fppf-stack conclusion for quasi-coherent sheaves locally generated
by at most an infinite cardinal is the relative stack `p κ S`. -/
@[stacks 04U7] #check
  (AlgebraicGeometry.QCohStack.Cardinal.instIsStackOnSite (κ := κ) (S := S) :
    IsStack.OnSite (Scheme.fppfTopology.over S)
      (AlgebraicGeometry.QCohStack.Cardinal.p κ S))

#check (AlgebraicGeometry.QCohStack.Cardinal.objectProperty_iff κ S)
#check (AlgebraicGeometry.Scheme.QCoh.isStack_aleph0 :
  (AlgebraicGeometry.Scheme.QCoh.kappaGenerated ℵ₀).fullsubcategory.IsStack
    AlgebraicGeometry.Scheme.fppfTopology)
#check (AlgebraicGeometry.QCohStack.Cardinal.exists_smallSubcategory κ S)
