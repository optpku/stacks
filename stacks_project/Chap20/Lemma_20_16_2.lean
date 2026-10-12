/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Sheaf.Cohomology.Cech.Compact
import StacksCheckRecall

@[expose] public section

/- Lemma 20.16.2 (09V2): on a Hausdorff quasi-compact space, the global Cech comparison
defined from the open-cover refinement system is an isomorphism in every degree.  The reusable
owner is functorial in the coefficient sheaf and provides an objectwise view. -/
@[stacks 09V2]
#check @TopCat.Sheaf.Cohomology.Cech.CompactHausdorff.isIsomorphic

#check @TopCat.Sheaf.Cohomology.Cech.RefinementComparison
#check @TopCat.Sheaf.Cohomology.Cech.RefinementComparison.IsColimitIso
#check @TopCat.Sheaf.Cohomology.Cech.Comparison.hom
#check @TopCat.Sheaf.Cohomology.Cech.Comparison.isIso
#check @TopCat.Sheaf.Cohomology.Cech.Comparison.iso
