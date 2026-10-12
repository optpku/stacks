/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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
