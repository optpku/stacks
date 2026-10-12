/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Inseparable
public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Topology.Sober
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Maps Lifting Specializations

This leaf contains map-level criteria for Mathlib's `SpecializingMap` and
`GeneralizingMap` predicates.
-/

@[expose] public section

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

namespace IsOpenMap

/-- Lemma 5.19.7 (2): a continuous open map from a Noetherian quasi-sober
space to a `T₀` space is generalizing. -/
@[stacks 0066 "open maps under Noetherian generic-point hypotheses lift generalizations"]
theorem generalizingMap_of_noetherianSpace_quasiSober_t0
    [TopologicalSpace.NoetherianSpace X] [QuasiSober X] [T0Space Y] {f : X → Y}
    (hopen : IsOpenMap f) (hf : Continuous f) :
    GeneralizingMap f := sorry

end IsOpenMap
