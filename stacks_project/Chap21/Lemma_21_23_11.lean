/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Cohomology.Acyclic.Comparison
import StacksCheckRecall

@[expose] public section

/- Lemma 21.23.11 (0BKZ): on a covering family of objects over which every cohomology sheaf is
acyclic, objectwise hypercohomology is the degree-zero cohomology of the corresponding
cohomology sheaf. -/
@[stacks 0BKZ]
#check @RingedSite.Hom.ModuleDerived.CohomologySheaves.cohomologyOverObject_isomorphic_zeroDegree

#check @RingedSite.Hom.ModuleSections.IsAcyclicOver
#check @RingedSite.Hom.ModuleSections.IsAcyclicOn
#check @RingedSite.Hom.ModuleDerived.CohomologySheaves.asDerived
#check @RingedSite.Hom.ModuleDerived.CohomologySheaves.IsAcyclicOn
#check @RingedSite.Hom.ModuleDerived.CohomologySheaves.IsAcyclicOn.over
#check @RingedSite.Hom.ModuleDerived.CohomologySheaves.IsAcyclicOn.toUniformNegative
