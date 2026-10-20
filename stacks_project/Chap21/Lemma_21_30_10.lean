module

public import ReasLib.CategoryTheory.Sites.TopologyComparison.Hypercohomology
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.30.10

The degreewise and bounded-below hypercohomology comparisons are owned by the reusable
`TopologyComparison.Hypercohomology` leaf.  This chapter file is only a source-facing recall
facade and has no dependency on another chapter.
-/

open CategoryTheory
open CategoryTheory.GrothendieckTopology
open CategoryTheory.GrothendieckTopology.TopologyComparison
open scoped CategoryTheory.GrothendieckTopology
  DerivedCategory.CohomologyIn GrothendieckTopologyDerivedSections

/- Lemma 21.30.10 (0EZH), clause (1): selected sheaf coefficients have the same degreewise
cohomology on the two slice topologies.  The first two recalls expose the canonical map and its
functorial form; the `AllVanishing` certificate from 0EZF remains explicit in the invertibility
views. -/
@[stacks 0EZH "(1), canonical map"]
#check @TopologyComparison.Cohomology.pullbackMap

@[stacks 0EZH "(1), functorial canonical map"]
#check @TopologyComparison.Cohomology.pullbackNatTrans

/- The invertibility and objectwise views require an explicit all-degree `(V_n)` certificate. -/
#check @Hypercohomology.pullbackMap_isIso_of_mem
#check @Hypercohomology.cohomology_isomorphic_of_mem

/- Lemma 21.30.10 (0EZH), clause (2): selected bounded-below complexes have the same
hypercohomology in every integer degree after the canonical inverse image; the all-degree
vanishing certificate is explicit in the reusable owner. -/
@[stacks 0EZH "(2)"]
#check @Hypercohomology.hypercohomology_isomorphic_of_plus

end
