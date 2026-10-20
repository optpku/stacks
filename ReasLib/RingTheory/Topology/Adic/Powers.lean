/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Topology.WeaklyAdmissible

/-! # Positive powers of ideals of definition -/

@[expose] public section

universe u

namespace TopologicalRing.Ideal.IsIdealOfDefinition

variable {A : Type u} [CommRing A] [TopologicalSpace A] [TopologicalRing.IsAdicRing A]

/-- Positive powers of an ideal of definition remain weak ideals of definition. -/
theorem isWeak_pow {I : Ideal A}
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) (n : ℕ) :
    TopologicalRing.Ideal.IsWeakIdealOfDefinition (I ^ (n + 1)) :=
  sorry

end TopologicalRing.Ideal.IsIdealOfDefinition
