/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Henselian
public import ReasLib.RingTheory.Topology.WeaklyAdmissible

/-!
# Henselian pairs from weakly admissible rings

Every weak ideal of definition in a weakly admissible topological ring defines
a henselian pair.
-/

@[expose] public section

universe u

namespace TopologicalRing.Ideal.IsWeakIdealOfDefinition

/-- A weak ideal of definition in a weakly admissible topological ring defines a henselian pair. -/
theorem henselianRing {A : Type u} [CommRing A] [TopologicalSpace A]
    [IsWeaklyAdmissibleRing A] {I : Ideal A}
    (hI : IsWeakIdealOfDefinition I) : HenselianRing A I := sorry

end TopologicalRing.Ideal.IsWeakIdealOfDefinition
