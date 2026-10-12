/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Gerbe.BaseChange
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 8.11.5 -- Base change of relative gerbes

The source-facing owner is the stack-in-groupoids specialization for arbitrary bilimit
pseudopullback cones.  Generic fibred-category and groupoid-fibred variants are recalled as
companions below, so downstream users can choose the weakest suitable assumptions.
-/

namespace CategoryTheory

@[stacks 06P3 "base change of gerbes over stacks"]
#check @StackOver.Groupoids.Hom.IsGerbeMorphism.baseChange

#check @FiberedCategoryOver.Hom.IsGerbeMorphism.baseChange
#check @FiberedCategoryOver.Groupoids.Hom.IsGerbeMorphism.baseChange
#check @CartesianBasedFunctor.IsGerbeMorphism.cartesianSnd

end CategoryTheory
