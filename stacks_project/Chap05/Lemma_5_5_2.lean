/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Bases.Generate
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 5.5.2

The generated-topology basis construction and its uniqueness theorem are owned
by `ReasLib.Topology.Bases.Generate`.
-/

/- The generated topology has the prescribed basis under the covering refinement hypotheses. -/
#check @TopologicalSpace.isTopologicalBasis_generateFrom

/- Lemma 5.5.2: the covering refinement family determines a unique topology with that basis. -/
@[stacks 0D5P "unique topology determined by the covering refinement family"]
#check @TopologicalSpace.existsUnique_topology_with_basis
