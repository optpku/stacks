/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Category.TopCat.Limits.Basic
import StacksCheckRecall

@[expose] public section

/- Lemma 5.29.1 (1): the category of topological spaces has all colimits. The core owner declaration
is the canonical mathlib instance `TopCat.topCat_hasColimits`. -/
@[stacks 0B1X "topological spaces have all colimits"]
#check TopCat.topCat_hasColimits

/- Lemma 5.29.1 (2): the forgetful functor from topological spaces to types preserves all
colimits. -/
@[stacks 0B1X "the forgetful functor from topological spaces preserves all colimits"]
#check TopCat.forget_preservesColimits
