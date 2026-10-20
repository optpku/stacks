/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Algebra.Ring.Taut
public import ReasLib.RingTheory.Topology.LocalMorphismProperty

/-!
# Locality of taut homomorphisms

Tautness of homomorphisms of countably indexed weakly admissible rings is
stable under étale-completion squares, descends along faithfully flat such
squares, and is stable under finite products of targets.
-/

@[expose] public section

universe u

namespace TopologicalRing

/-- Tautness of homomorphisms of countably indexed weakly admissible rings
satisfies étale-completion ascent, faithfully flat descent, and stability
under finite products of targets. -/
theorem isLocalMorphismProperty_isTaut :
    IsLocalMorphismProperty
      fun {A B : Type u}
        [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
        [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B]
        (φ : B →+* A) ↦ φ.IsTaut :=
  sorry

end TopologicalRing
