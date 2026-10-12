/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import StacksCheckRecall.CommandCrossRef

public import ReasLib.CategoryTheory.Sites.Localization.Representable.LowerShriek
import StacksCheckRecall

@[expose] public section

/- Lemma 7.25.7 (03EE): under representable localization, lower shriek after slice pullback is
canonically the slice functor `Over.star`. -/
@[stacks 03EE] #check @CategoryTheory.GrothendieckTopology.RepresentableLocalization.lowerShriekOverPullbackComparison_isIso
