module

public import ReasLib.CategoryTheory.Sites.TopologyComparison.Hypercohomology
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.30.4

The hypercohomology comparison is owned by `ReasLib`.  This chapter file is intentionally a
source-facing recall facade, so later chapters can import the reusable declaration without a
reverse dependency on Chap21.
-/

open CategoryTheory
open scoped CategoryTheory CategoryTheory.GrothendieckTopology
  GrothendieckTopology GrothendieckTopologyDerivedSections

/- Lemma 21.30.4 (0EZB): hypercohomology comparison under `(V_n)`. -/
@[stacks 0EZB]
#check @CategoryTheory.GrothendieckTopology.TopologyComparison.Hypercohomology.isomorphic_of_conditionV

end
