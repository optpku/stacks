/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.CategoryTheory.Pretriangulated.BrownRepresentability.SmallSet
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.38.1

The compactly generated Brown theorem and its canonical `Type`-valued
representability companion are owned by the neutral Brown-representability
leaf, using only coproducts indexed in the Hom universe.
-/

@[stacks 0A8F] #check @CategoryTheory.BrownRepresentability.SmallSet.ofCompactGeneration

#check @CategoryTheory.BrownRepresentability.SmallSet.isRepresentable_ofCompactGeneration
