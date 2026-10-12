/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Cech.Cofinal.FixedTargetFinite
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.16.1

The finite cofinal covering system and its filtered-colimit cohomology comparison are owned by
`Sheaf.Cech.CofinalSystem.FiniteCoverings`.  This chapter file is the source-facing recall only;
downstream developments should import the ReasLib leaf directly.
-/

open CategoryTheory CategoryTheory.Limits Opposite

/- Lemma 21.16.1 (0739): a finite fixed-target cofinal Cech system gives a canonical filtered-
colimit comparison for objectwise sheaf cohomology. -/
@[stacks 0739 "finite fixed-target cofinal Cech comparison"]
#check @CategoryTheory.Sheaf.Cech.FixedTarget.cohomologyOverObject_colimitComparison_isIso

#check @CategoryTheory.Sheaf.Cech.FixedTarget.FiniteCoverings
#check @CategoryTheory.Sheaf.Cech.FixedTarget.FiniteCoverings.members_mem
#check @CategoryTheory.Sheaf.Cech.FixedTarget.FiniteCoverings.exists_refinement

end
