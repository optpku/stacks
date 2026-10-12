/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Catenary
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 5.11.6

The reusable finite-and-additive codimension characterization is owned by
`ReasLib.Topology.Catenary`.
-/

/- Lemma 5.11.6: catenarity is equivalent to finite, additive relative codimension. -/
@[stacks 02I6]
#check @TopologicalSpace.catenarySpace_iff_finite_codimBetween_and_codimBetween_additive
