/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Sheaf.Cohomology.Cech.LowDegree
import StacksCheckRecall

@[expose] public section

/- Lemma 20.16.1 (09V1): the map from global degree-one Cech cohomology to sheaf cohomology
defined by the open-cover refinement comparison is an isomorphism.  The reusable owner retains
the concrete comparison and its coverwise torsor-class specification. -/
@[stacks 09V1]
#check @TopCat.Sheaf.Cohomology.Cech.DegreeOne.isIsomorphic

#check @TopCat.Sheaf.Cohomology.Cech.DegreeOne.ClassMap
#check @TopCat.Sheaf.Cohomology.Cech.DegreeOne.IsCoverwise
#check @TopCat.Sheaf.Cohomology.Cech.DegreeOne.CoverwiseComparison
#check @TopCat.Sheaf.Cohomology.Cech.DegreeOne.isColimitIso
#check @TopCat.Sheaf.Cohomology.Cech.DegreeOne.comparison_isIso
#check @TopCat.Sheaf.Cohomology.Cech.DegreeOne.CoverwiseComparison.iso
