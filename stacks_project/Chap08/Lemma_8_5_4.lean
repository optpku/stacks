/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.Equivalence
import StacksCheckRecall

@[expose] public section

/-!
# Equivalence invariance for stacks in groupoids

The stack-in-groupoids iff is a shared owner theorem. No second transport proof belongs in this
chapter file.
-/

namespace CategoryTheory

/- Lemma 8.5.4: stack-in-groupoids conditions are invariant under an equivalence over the base. -/
@[stacks 042X]
#check @IsStack.InGroupoids.iff_of_isEquivalence

end CategoryTheory
