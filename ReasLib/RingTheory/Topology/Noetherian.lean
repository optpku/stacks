/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Noetherian.Basic
public import ReasLib.RingTheory.Topology.Adic.Complete
public import ReasLib.RingTheory.Topology.CountablyIndexed
public import ReasLib.RingTheory.Topology.WeakIdealCompletion.Properties

/-!
# Noetherian adic rings

Noetherian adic rings are countably indexed, and weak-ideal completion of a
Noetherian algebra over a Noetherian adic ring is adic.
-/

@[expose] public section

universe u

namespace TopologicalRing.Noetherian

/-- Every Noetherian adic ring admits a countable basis of open ideals at zero. -/
instance instIsCountablyIndexed {A : Type u}
    [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A] :
    IsCountablyIndexed A := sorry

end TopologicalRing.Noetherian

namespace TopologicalRing.weakIdealCompletion

/-- The weak-ideal completion of a Noetherian algebra over a Noetherian adic
ring remains adic. -/
instance instIsAdicRing {A A' : Type u}
    [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
    [CommRing A'] [Algebra A A'] [IsNoetherianRing A'] :
    IsAdicRing (weakIdealCompletion A A') :=
  (isAdicRing_and_isNoetherianRing (A := A) (A' := A')).1

end TopologicalRing.weakIdealCompletion
