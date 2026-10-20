/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Sheaf.Cohomology.Profinite
import StacksCheckRecall

@[expose] public section

/- Lemma 20.22.3 (0A3F): on a profinite space, global sections of abelian sheaves are exact;
equivalently, every abelian sheaf has vanishing global cohomology in positive degree. -/
@[stacks 0A3F]
#check @TopCat.Sheaf.Cohomology.Profinite.isZero_higherCohomology

#check @TopCat.Sheaf.Cohomology.Profinite.isZero_atTop
#check @TopCat.Sheaf.Cohomology.Profinite.isZero_global
#check @TopCat.Sheaf.GlobalSections.Profinite.map_surjective
#check @TopCat.Sheaf.GlobalSections.Profinite.preservesEpimorphisms
#check @TopCat.Sheaf.GlobalSections.Profinite.exactSections
#check @TopCat.Sheaf.GlobalSections.Profinite.sectionsPreservesFiniteColimits
#check @TopCat.Sheaf.GlobalSections.Profinite.gammaPreservesEpimorphisms
#check @TopCat.Sheaf.GlobalSections.Profinite.gammaPreservesFiniteColimits
#check @TopCat.Sheaf.GlobalSections.Profinite.exactGlobalSections
