/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Algebra.LinearTopology.Completion

@[expose] public section

universe u v w

namespace IsLinearTopology

/- Lemma 87.4.3 completion API. -/
#check (IsLinearTopology.Completion.of :
  ∀ {R : Type u} {M : Type v}
    [Ring R] [AddCommGroup M] [Module R M] [TopologicalSpace M]
    [IsLinearTopology R M],
    M →ₗ[R] IsLinearTopology.Completion R M)

end IsLinearTopology
