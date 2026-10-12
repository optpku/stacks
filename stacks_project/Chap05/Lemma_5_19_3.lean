/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Specialization.Stable
import StacksCheckRecall

@[expose] public section

/- Lemma 5.19.3: a specialization-stable subset is a directed union of
closed subsets. -/
@[stacks 0EES]
#check @stableUnderSpecialization_iff_exists_directedCloseds_sUnion_eq
