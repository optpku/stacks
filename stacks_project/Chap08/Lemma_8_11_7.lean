/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Gerbe.BaseChange
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 8.11.7 -- Detection after base change

The source-facing owner is the stack-in-groupoids specialization for arbitrary bilimit
pseudopullback cones.  Generic fibred-category and groupoid-fibred variants are recalled as
companions below, exposing the weaker hypotheses without changing the source-level entry.
-/

namespace CategoryTheory

@[stacks 06P4 "detecting gerbes after base change"]
#check @StackOver.Groupoids.Hom.IsGerbeMorphism.ofBaseChange

#check @FiberedCategoryOver.Hom.IsGerbeMorphism.ofBaseChange
#check @FiberedCategoryOver.Groupoids.Hom.IsGerbeMorphism.ofBaseChange
#check @CartesianBasedFunctor.IsGerbeMorphism.of_cartesianSnd
#check @BasedCategory.PseudoPullback.cartesianSnd.isGerbeMorphism_iff

end CategoryTheory
