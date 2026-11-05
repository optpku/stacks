/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Depth
public import ReasLib.RingTheory.LocalRing.Kollar

/-!
# Kollar's local-ring criterion

This leaf owns the four-way local-ring alternative.  The exceptional branch is
the predicate from `ReasLib.RingTheory.LocalRing.Kollar`, while this file keeps
the criterion itself independent of chapter-facing proofs and imports.
-/

@[expose] public section

universe u

namespace IsLocalRing.Kollar

/-- The four alternatives in Kollar's criterion, in their order in Stacks 0BHZ. -/
def alternative (R : Type u) [CommRing R] [IsLocalRing R] : Fin 4 → Prop :=
  ![IsArtinianRing R,
    IsRegularLocalRing R ∧ ringKrullDim R = 1,
    (2 : WithTop ℕ) ≤ moduleDepth R R,
    HasExceptionalExtension R]

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- Kollar's local-ring criterion: exactly one of the Artinian,
regular-dimension-one, depth-at-least-two, and exceptional-extension alternatives holds. -/
@[stacks 0BHZ "Kollar local-ring criterion"]
theorem exactlyOne [IsNoetherianRing R] :
    ∃! i : Fin 4, alternative R i := sorry

variable [IsNoetherianRing R]

/-- Depth at least two excludes Kollar's exceptional finite-extension alternative. -/
@[stacks 0BHZ "depth excludes Kollar exceptional extensions"]
theorem notExceptionalOfDepthTwo
    (hdepth : (2 : WithTop ℕ) ≤ moduleDepth R R) :
    ¬ HasExceptionalExtension R := sorry

end IsLocalRing.Kollar
