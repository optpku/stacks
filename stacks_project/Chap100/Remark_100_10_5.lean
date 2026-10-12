/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap100.Remark_100_10_5_Reduction
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicStack TopologicalSpace CategoryTheory
open AlgebraicGeometry.Groupoids.Hom

universe u

/- Remark 100.10.5: a locally closed subset `T ⊂ Points X` of an algebraic stack
`X` over a scheme `S` has a reduced induced substack structure, obtained as the
reduced closed substack of the open substack `U` with
`U.pointsSet = Points X \ ∂T`, where `∂T = closure T \ T`. -/
@[stacks 06FK] #check AlgebraicStack.LocallyClosedReduction.boundary
@[stacks 06FK] #check AlgebraicStack.LocallyClosedReduction.ambientOpen
@[stacks 06FK] #check AlgebraicStack.LocallyClosedReduction.closedSubset
@[stacks 06FK] #check AlgebraicStack.LocallyClosedReduction.closedStructure
@[stacks 06FK] #check AlgebraicStack.LocallyClosedReduction.stack
@[stacks 06FK] #check AlgebraicStack.LocallyClosedReduction.ιToAmbientOpen
@[stacks 06FK] #check AlgebraicStack.LocallyClosedReduction.ι
@[stacks 06FK] #check AlgebraicStack.LocallyClosedReduction.range_ι
@[stacks 06FK] #check AlgebraicStack.LocallyClosedSubstack.reduced

section

variable {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
  (T : LocallyCloseds (Points X))

#check (inferInstance : OpenImmersion (LocallyClosedReduction.ambientOpen T).ι)
#check (inferInstance : ClosedImmersion (LocallyClosedReduction.ιToAmbientOpen T))
#check (inferInstance : Immersion (LocallyClosedReduction.ι T))
#check (inferInstance : IsReduced (LocallyClosedReduction.stack T))
#check LocallyClosedReduction.coborder_eq_compl_boundary T

end
