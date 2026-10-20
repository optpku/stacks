module

import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Existence
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.41.6

The existence and comparison results are stated through the reusable
integer-indexed shifted-Hom vanishing API for finite Postnikov systems.
-/

@[stacks 0D83] #check @CategoryTheory.PostnikovSystem.Existence.nonempty

@[stacks 0D83] #check @CategoryTheory.PostnikovSystem.Morphism.Existence.comparison
#check @CategoryTheory.PostnikovSystem.Morphism.IsLevelwiseIso.yMap
