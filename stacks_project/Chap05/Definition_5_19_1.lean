/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Inseparable
import StacksCheckRecall

@[expose] public section

/- Definition 5.19.1 (1): the canonical relation expressing that one point specializes to
another. -/
@[stacks 0061 "the specialization relation"]
#check Specializes

/- Companion check: `x` is a specialization of `x'`, equivalently `x'` is a generalization of
`x`, exactly when `x ∈ closure ({x'} : Set X)`. -/
#check specializes_iff_mem_closure

/- Definition 5.19.1 (2): a subset stable under specialization is the canonical predicate
`StableUnderSpecialization`. -/
@[stacks 0061 "subsets stable under specialization"]
#check StableUnderSpecialization

/- Definition 5.19.1 (3): a subset stable under generalization is the canonical predicate
`StableUnderGeneralization`. -/
@[stacks 0061 "subsets stable under generalization"]
#check StableUnderGeneralization
