/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Monoidal.Closed.Exactness
import StacksCheckRecall

/-!
# Lemma 18.27.4

The four presheaf/sheaf clauses are instances of two categorical facts about internal Hom in a
braided closed monoidal category.  The reusable owners are independent of sites and modules.
-/

@[expose] public section

/- Lemma 18.27.4 (1) (03EN): presheaf internal Hom preserves limits in its target. -/
@[stacks 03EN "(1)"]
#check @CategoryTheory.MonoidalClosed.ihom_preservesLimits

/- Lemma 18.27.4 (2) (03EN): presheaf internal Hom sends source colimits to limits. -/
@[stacks 03EN "(2)"]
#check @CategoryTheory.MonoidalClosed.internalHomFlip_preservesLimits

/- Lemma 18.27.4 (3) (03EN): sheaf internal Hom preserves limits in its target. -/
@[stacks 03EN "(3)"]
#check @CategoryTheory.MonoidalClosed.ihom_preservesLimits

/- Lemma 18.27.4 (4) (03EN): sheaf internal Hom sends source colimits to limits. -/
@[stacks 03EN "(4)"]
#check @CategoryTheory.MonoidalClosed.internalHomFlip_preservesLimits
