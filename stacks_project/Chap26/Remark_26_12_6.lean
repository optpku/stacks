/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.LocallyClosedReduction
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open TopologicalSpace

universe u

/- Remark 26.12.6: a locally closed subset has a canonical reduced induced scheme in the open
complement of its boundary. -/
@[stacks 0F2L] #check Scheme.LocallyClosedReduction.ambientOpen
@[stacks 0F2L] #check Scheme.LocallyClosedReduction.closedSubset
@[stacks 0F2L] #check Scheme.LocallyClosedReduction.closedStructure
#check Scheme.LocallyClosedReduction.ideal
@[stacks 0F2L] #check Scheme.LocallyClosedReduction.scheme
@[stacks 0F2L] #check Scheme.LocallyClosedReduction.ιToAmbientOpen
@[stacks 0F2L] #check Scheme.LocallyClosedReduction.range_ιToAmbientOpen
@[stacks 0F2L] #check Scheme.LocallyClosedReduction.ι
@[stacks 0F2L] #check Scheme.LocallyClosedReduction.range_ι

section

variable {X : Scheme.{u}} (T : LocallyCloseds X)

#check (inferInstance : IsReduced (Scheme.LocallyClosedReduction.scheme T))
#check (inferInstance : IsImmersion (Scheme.LocallyClosedReduction.ι T))

end
