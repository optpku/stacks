/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Topology.Adic.Weakly
public import ReasLib.Topology.Algebra.Ring.Taut

/-!
# Taut ascent of weakly pre-adic structures
-/

@[expose] public section

universe u v

namespace TopologicalRing.Ideal

/-- A continuous taut homomorphism maps a weakly adic ideal to a weakly adic ideal. -/
theorem IsWeaklyAdic.map_of_isTaut {A : Type u} {B : Type v}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    {φ : A →+* B} (hcont : Continuous φ) (htaut : φ.IsTaut) {I : Ideal A}
    (hI : IsWeaklyAdic I) : IsWeaklyAdic (Ideal.map φ I) := sorry

end TopologicalRing.Ideal

namespace TopologicalRing.IsWeaklyPreadicRing

/-- A continuous taut homomorphism carries a weakly pre-adic source ring to a weakly
pre-adic target ring. -/
theorem of_isTaut {A : Type u} {B : Type v}
    [CommRing A] [TopologicalSpace A] [IsWeaklyPreadicRing A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    {φ : A →+* B} (hcont : Continuous φ) (htaut : φ.IsTaut) :
    IsWeaklyPreadicRing B := sorry

end TopologicalRing.IsWeaklyPreadicRing
