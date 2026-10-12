/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.ConstructibleTopology.Specialization
import StacksCheckRecall

@[expose] public section

/- Lemma 5.23.6 (1): ordinary closure of a constructibly closed subset is
controlled by specialization. -/
@[stacks 0903 "specializing points"]
#check IsClosed.exists_specializingPoint_of_mem_closure

/- Lemma 5.23.6 (2): specialization-stable constructibly closed subsets are
closed. -/
@[stacks 0903 "closedness"]
#check IsClosed.isClosed_of_constructibleTopology_of_stableUnderSpecialization

/- Lemma 5.23.6 (3): generalization-stable constructibly open subsets are
open. -/
@[stacks 0903 "openness"]
#check IsOpen.isOpen_of_constructibleTopology_of_stableUnderGeneralization
