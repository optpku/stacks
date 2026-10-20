/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Topology.Basic
import StacksCheckRecall

@[expose] public section

/-
`TopModuleCat R` is the canonical bundled owner for the source notion: `TopModuleCat.of` accepts
exactly an `R`-module topology with `ContinuousAdd` and `ContinuousSMul`. The owner stores the
derived continuity of negation as part of `IsTopologicalAddGroup`. In contrast, `moduleTopology`
is the particular finest topology with these properties, so it is not the definition recalled by
the source. Morphisms are canonically bundled as `ContinuousLinearMap`.
-/

/- Definition 5.30.10 (1): a topological module over a topological ring is canonically bundled as
`TopModuleCat R`. -/
@[stacks 0B25 "topological modules over a topological ring"]
#check TopModuleCat

/- Definition 5.30.10 (2): homomorphisms of topological modules are canonically bundled as
continuous linear maps. -/
@[stacks 0B25 "continuous homomorphisms of topological modules"]
#check ContinuousLinearMap
