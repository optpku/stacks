module

import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Uniqueness
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.41.5

The three Hom-vanishing alternatives and their common uniqueness conclusion
are owned by the neutral Postnikov-system morphism API.
-/

#check @CategoryTheory.PostnikovSystem.Morphism.Uniqueness.vanishing

@[stacks 0FXE] #check @CategoryTheory.PostnikovSystem.Morphism.Uniqueness.subsingleton
