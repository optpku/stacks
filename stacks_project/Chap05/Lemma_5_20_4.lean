/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Specialization.Dimension.Catenary
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 5.20.4

The reusable local-existence API is owned by
`ReasLib.Topology.Specialization.Dimension.Catenary`.
-/

/- Lemma 5.20.4: every point of a locally Noetherian sober catenary space has an open
neighbourhood whose induced topology admits a dimension function. -/
@[stacks 02IC]
#check @TopologicalSpace.CatenarySpace.exists_open_dimensionFunction
