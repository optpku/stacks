/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.CategoryTheory.Pretriangulated.BrownRepresentability
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.38.1

The compactly generated Brown theorem and its canonical `Type`-valued
representability companion are owned by the neutral Brown-representability
leaf.
-/

@[stacks 0A8F] #check @CategoryTheory.BrownRepresentability.ofCompactGeneration

#check @CategoryTheory.BrownRepresentability.isRepresentable_ofCompactGeneration
