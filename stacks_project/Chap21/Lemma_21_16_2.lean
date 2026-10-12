/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.QuasiCompact.TestSet.Cohomology
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.16.2

The cohomological test-set package and its bridge to the canonical quasi-compact test-set API are
owned by `GrothendieckTopology.Cohomology`.  This chapter entry is a source-facing recall.
-/

open CategoryTheory CategoryTheory.Limits

/- Lemma 21.16.2 (0GN3): a site-level collection of set-valued sheaves satisfying the
surjectivity, product, equalizer, and quasi-compactness clauses makes filtered colimits commute
with every degree of abelian sheaf cohomology. -/
@[stacks 0GN3]
#check @CategoryTheory.GrothendieckTopology.Cohomology.colimitComparison_isIso

#check @CategoryTheory.GrothendieckTopology.Cohomology.TestSet
#check @CategoryTheory.GrothendieckTopology.Cohomology.TestSet.toQuasiCompactTestSet
#check @CategoryTheory.GrothendieckTopology.Cohomology.testSet_iff

end
