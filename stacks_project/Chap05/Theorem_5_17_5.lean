/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Maps.Proper.Characterization
import StacksCheckRecall

@[expose] public section

/- Theorem 5.17.5: the four standard continuous proper-map formulations are
equivalent. -/
@[stacks 005R]
#check @Continuous.isProperMap_tfae
