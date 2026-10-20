/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Constructible.Neighborhood
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Constructible Sets Stable under Specialization

This module gives the closed and open forms of the constructible stability
criterion in Noetherian quasi-sober spaces.
-/

@[expose] public section

universe u

open Set TopologicalSpace Topology

namespace Topology.IsConstructible

variable {X : Type u} [TopologicalSpace X] [NoetherianSpace X] [QuasiSober X]

/-- In a Noetherian quasi-sober space, a constructible subset stable under specialization is
closed. -/
@[stacks 0542 "constructible and specialization-stable implies closed"]
theorem isClosed_of_stableUnderSpecialization {E : Set X}
    (hE : IsConstructible E) (hE_spec : StableUnderSpecialization E) : IsClosed E := sorry

/-- In a Noetherian quasi-sober space, a constructible subset stable under generalization is
open. -/
@[stacks 0542 "constructible and generalization-stable implies open"]
theorem isOpen_of_stableUnderGeneralization {E : Set X}
    (hE : IsConstructible E) (hE_gen : StableUnderGeneralization E) : IsOpen E := sorry

end Topology.IsConstructible
