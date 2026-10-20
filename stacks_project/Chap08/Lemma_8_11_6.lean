/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Gerbe.Over
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 8.11.6 -- Composition of relative gerbes

The closure theorem is a property-level operation on stack gerbe morphisms, independent of the
chapter.
-/

namespace CategoryTheory

@[stacks 06R3 "composition of gerbes over stacks"]
#check @StackOver.Groupoids.Hom.IsGerbeMorphism.comp

#check @CartesianBasedFunctor.IsGerbeMorphism.comp
#check @FiberedCategoryOver.Hom.IsGerbeMorphism.comp

end CategoryTheory
