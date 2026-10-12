/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Category.LCCat.Limits
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

/- Lemma 21.31.1: the category `LC` has pullbacks, a terminal object, and therefore finite
limits. Pullbacks whose two source spaces are compact are compact. -/
@[stacks 09WZ "(1)"]
#check LCCat.instHasPullbacks

@[stacks 09WZ "(2)"]
#check LCCat.instHasTerminal

@[stacks 09WZ "(3)"]
#check LCCat.instHasFiniteLimits

@[stacks 09WZ "(4)"]
#check @LCCat.compactSpace_pullback

/- The compactness clause is owned at the more general `TopCat` level: only the two source
spaces need be compact, while the target need only be Hausdorff. -/
@[stacks 09WZ "(4), generalized"]
#check @TopCat.compactSpace_pullback
