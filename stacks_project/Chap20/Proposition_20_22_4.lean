/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Sheaf.Cohomology.Spectral
import StacksCheckRecall

@[expose] public section

/- Proposition 20.22.4 (1) (0A3G): on a spectral space of Krull dimension at most `d`,
abelian-sheaf cohomology vanishes in degrees strictly larger than `d`. -/
@[stacks 0A3G "(1)"]
#check @TopCat.Sheaf.Cohomology.Spectral.isZero_of_krullDim_le

/- Proposition 20.22.4 (2) (0A3G): in degree `d`, global restriction to every compact open is
surjective. -/
@[stacks 0A3G "(2)"]
#check @TopCat.Sheaf.Cohomology.Spectral.globalRestriction_surjective_of_krullDim_le

/- Proposition 20.22.4 (3) (0A3G): cohomology with support in a constructible closed subset
vanishes in degrees strictly larger than `d`. -/
@[stacks 0A3G "(3)"]
#check @TopCat.Sheaf.Cohomology.Spectral.support_isZero_of_krullDim_le

#check @TopCat.Sheaf.Cohomology.Spectral.supportHasDimensionLE_of_krullDim_le
#check @TopCat.Sheaf.ClosedSubset.GlobalSectionsWithSupport.functorH
#check @TopCat.Sheaf.ClosedSubset.GlobalSectionsWithSupport.H
