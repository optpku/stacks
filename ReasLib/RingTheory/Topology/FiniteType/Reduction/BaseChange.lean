/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Topology.FiniteType.Reduction
public import ReasLib.RingTheory.Topology.WeaklyAdmissible.BaseChange

/-!
# Finite type on reductions is stable under completed base change
-/

@[expose] public section

universe u

open TopologicalRing RingHom

namespace TopologicalRing

/-- Finite type of the induced map on topological-nilradical quotients of
countably indexed weakly admissible rings is stable under completed base change. -/
theorem isStableUnderBaseChange_isFiniteTypeOnReduction :
    IsLocalMorphismProperty.IsStableUnderBaseChange
      fun {A B : Type u}
        [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
        [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B]
        (φ : B →+* A) ↦ φ.IsFiniteTypeOnReduction :=
  sorry

end TopologicalRing
