/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Definition_66_12_5_Structure
public import stacks_project.Chap66.Definition_66_12_5_Reduced
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open TopologicalSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} (X : AlgebraicSpace S) (Z : Closeds (Points X))

/- Definition 66.12.5 (1): an algebraic space structure on a closed subset `Z` of `Points X` is a
closed subspace `Z'` of `X` with `Z'.pointsSet` equal to `Z`. -/
@[stacks 047X] #check ClosedSubspaceStructure Z
#check ClosedSubspaceStructure.ofSubspace
#check ClosedSubspaceStructure.space
#check ClosedSubspaceStructure.ι
#check ClosedSubspaceStructure.spec

/- Definition 66.12.5 (2): the reduced induced algebraic space structure on `Z` is the one
constructed in Lemma 66.12.3. -/
@[stacks 047X] #check ClosedSubspaceStructure.reduced Z
#check ClosedSubspaceStructure.reduced_spec

/- Definition 66.12.5 (3): the reduction `X_red` of `X` is the reduced induced algebraic space
structure on `Points X`. -/
@[stacks 047X] #check reduction
#check reductionι
#check reduction_spec

end AlgebraicGeometry.AlgebraicSpace
