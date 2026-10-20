/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Sheaf.Cohomology.Cech.LowDegree
import StacksCheckRecall

@[expose] public section

/- Lemma 20.16.1 (09V1): the source-defined map from global degree-one Cech cohomology to sheaf
cohomology is an isomorphism.  The reusable owner retains the concrete comparison and its
coverwise torsor-class specification. -/
@[stacks 09V1]
#check @TopCat.Sheaf.Cohomology.Cech.DegreeOne.isIsomorphic

#check @TopCat.Sheaf.Cohomology.Cech.DegreeOne.ClassMap
#check @TopCat.Sheaf.Cohomology.Cech.DegreeOne.IsCoverwise
#check @TopCat.Sheaf.Cohomology.Cech.DegreeOne.CoverwiseComparison
#check @TopCat.Sheaf.Cohomology.Cech.DegreeOne.CoverwiseComparison.canonicalComparison
#check @TopCat.Sheaf.Cohomology.Cech.DegreeOne.isColimitIso
#check @TopCat.Sheaf.Cohomology.Cech.DegreeOne.comparison_isIso
#check @TopCat.Sheaf.Cohomology.Cech.DegreeOne.CoverwiseComparison.iso
