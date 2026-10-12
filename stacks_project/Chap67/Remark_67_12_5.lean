/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Remark_67_12_5_Opens
public import stacks_project.Chap67.Remark_67_12_5_Reduction
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicSpace TopologicalSpace CategoryTheory

universe u

/- Remark 67.12.5: a locally closed subset `T ⊂ Points X` of an algebraic space
`X` over a scheme `S` has a reduced induced subspace structure, obtained as the
reduced closed subspace of the open subspace `U` with
`U.pointsSet = Points X \ ∂T`, where `∂T = closure T \ T`. -/
@[stacks 06EC] #check AlgebraicSpace.LocallyClosedReduction.boundary
@[stacks 06EC] #check AlgebraicSpace.LocallyClosedReduction.ambientOpen
@[stacks 06EC] #check AlgebraicSpace.LocallyClosedReduction.closedSubset
@[stacks 06EC] #check AlgebraicSpace.LocallyClosedReduction.closedStructure
@[stacks 06EC] #check AlgebraicSpace.LocallyClosedReduction.space
@[stacks 06EC] #check AlgebraicSpace.LocallyClosedReduction.ιToAmbientOpen
@[stacks 06EC] #check AlgebraicSpace.LocallyClosedReduction.range_ιToAmbientOpen
@[stacks 06EC] #check AlgebraicSpace.LocallyClosedReduction.ι
@[stacks 06EC] #check AlgebraicSpace.LocallyClosedReduction.range_ι
@[stacks 06EC] #check AlgebraicSpace.LocallyClosedReduction.isReduced_space
@[stacks 06EC] #check AlgebraicSpace.LocallyClosedSubspace.reduced

section

variable {S : Scheme.{u}} {X : AlgebraicSpace S} (T : LocallyCloseds (Points X))

#check (inferInstance : IsOpenImmersion (LocallyClosedReduction.ambientOpen T).ι)
#check (inferInstance : IsClosedImmersion (LocallyClosedReduction.ιToAmbientOpen T))
#check (inferInstance : IsImmersion (LocallyClosedReduction.ι T))
#check LocallyClosedReduction.coborder_eq_compl_boundary T

end

