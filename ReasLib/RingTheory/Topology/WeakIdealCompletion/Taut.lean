/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Topology.WeakIdealCompletion.Kernel
public import ReasLib.RingTheory.Topology.WeakIdealCompletion.Map
public import ReasLib.Topology.Algebra.Ring.Taut

/-!
# Tautness of the weak-ideal completion map

The canonical map from a weakly admissible base ring to the weak-ideal completion
of any algebra over it is taut.
-/

@[expose] public section

noncomputable section

universe u

namespace TopologicalRing.weakIdealCompletion

variable {B A : Type u} [CommRing B] [TopologicalSpace B] [CommRing A] [Algebra B A]
  [IsWeaklyAdmissibleRing B]

/-- The canonical algebra map from a weakly admissible ring to the weak-ideal
completion of an algebra over it is taut. -/
theorem isTaut_algebraMap : (algebraMap B (weakIdealCompletion B A)).IsTaut :=
  sorry

end TopologicalRing.weakIdealCompletion
