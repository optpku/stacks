/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Sheaf.Cohomology.InverseLimit
import StacksCheckRecall

@[expose] public section

/- Lemma 20.19.3 (0A37): for a cofiltered inverse system of spectral spaces with spectral
transition maps and compatible abelian sheaves, cohomology over a compact open commutes with the
canonical inverse-limit colimit construction. -/
@[stacks 0A37]
#check @TopCat.Sheaf.InverseLimit.Cohomology.comparison_isIso

#check @TopCat.Sheaf.InverseLimit.Cohomology.transition
#check @TopCat.Sheaf.InverseLimit.Cohomology.diagram
#check @TopCat.Sheaf.InverseLimit.Cohomology.stageMap
#check @TopCat.Sheaf.InverseLimit.Cohomology.cocone
#check @TopCat.Sheaf.InverseLimit.Cohomology.comparison
#check @TopCat.Sheaf.InverseLimit.Cohomology.ι_comp_comparison
