/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import StacksCheckRecall.CommandCrossRef

public import ReasLib.CategoryTheory.Sites.WeaklyContractible
import StacksCheckRecall

/- Lemma 7.40.1: weak contractibility is characterized by splittings of canonical sheafified
cover maps. The reusable owner is in ReasLib. -/
#check @CategoryTheory.GrothendieckTopology.IsWeaklyContractible
@[stacks 090K] #check @CategoryTheory.GrothendieckTopology.IsWeaklyContractible.iff_isSplitEpi_coverMap
