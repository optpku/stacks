/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.CategoryTheory.Pretriangulated.Triangle.Endomorphism
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.4.6

Compatible outer idempotents are lifted by the reusable distinguished-triangle
endomorphism API; its result retains the entire triangle endomorphism, not
only the middle component.
-/

@[stacks 05QQ] #check @CategoryTheory.Pretriangulated.Triangle.Endomorphism.existsIdempotentOfOuter
