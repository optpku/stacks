/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.Coverwise
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 8.4.2 — Bridge

Lemma 8.4.2 characterizes stacks via coverwise descent equivalences. Its canonical owner is
`CategoryTheory.IsStack.OnSite.iff_coverwise`; `IsStack.OnSite.Descent.isStackFor_iff` is the
fixed-cover bridge used to formulate the criterion.
-/

namespace CategoryTheory

@[stacks 02ZF]
#check @IsStack.OnSite.iff_coverwise

#check @IsStack.OnSite.Descent.isStackFor_iff
#check @IsStack.OnSite.Descent.isEquivalence

end CategoryTheory
