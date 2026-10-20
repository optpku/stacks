/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.TopologyComparison.Situation
import StacksCheckRecall

@[expose] public section

/-!
# Situation 21.30.1

The comparison situation, its local vanishing predicate, and the coefficient subcategory `A_X`
are reusable topology-comparison infrastructure owned by `ReasLib`.
-/

open CategoryTheory

/- Situation 21.30.1 (0EZ3): comparison data for cohomology on two topologies. -/
@[stacks 0EZ3]
#check @GrothendieckTopology.TopologyComparison.Situation

@[stacks 0EZ3 "finer-topology coefficient sheaf"]
#check @GrothendieckTopology.TopologyComparison.Situation.finerSheaf

@[stacks 0EZ3 "finer-topology coefficient comparison isomorphism"]
#check @GrothendieckTopology.TopologyComparison.Situation.finerSheafIsoPullback

@[stacks 0EZ3 "generic finer-sheaf comparison isomorphism"]
#check @GrothendieckTopology.comparisonTopologyPullbackIsoOfIsSheaf

@[stacks 0EZ3 "generic comparison-unit specification"]
#check @GrothendieckTopology.comparisonTopology_unit_app_eq_pullbackIso_inv

@[stacks 0EZ3 "local comparison vanishing"]
#check @GrothendieckTopology.TopologyComparison.Situation.LocalVanishing

end
