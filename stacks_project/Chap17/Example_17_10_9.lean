/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Associated.RealBouquet
import StacksCheckRecall

/-!
# Example 17.10.9

The explicit real-bouquet counterexample and all of its construction API are owned by ReasLib.
-/

@[expose] public section

noncomputable section

namespace AlgebraicGeometry.RingedSpace.Module.Associated.RealBouquet

#check @cutoff
#check @branchCoefficient
#check @targetRow.project_same
#check @freeSheafMap
#check @associatedMap
#check @not_isInducedOn_standardNeighborhood

/- Example 17.10.9 (01BL): there is a morphism between associated free module sheaves which is
not induced by a module homomorphism on any neighborhood of the bouquet origin. -/
@[stacks 01BL "not locally induced"]
#check @not_isLocallyInducedAt

end AlgebraicGeometry.RingedSpace.Module.Associated.RealBouquet
