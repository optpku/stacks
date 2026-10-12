/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Topology.WeaklyAdmissible
public import ReasLib.Topology.Algebra.Ring.Taut
public import ReasLib.RingTheory.Topology.TopologicalNilradical

/-!
# Taut ascent of weakly pre-admissible rings
-/

@[expose] public section

universe u v

namespace TopologicalRing.Ideal.IsWeakIdealOfDefinition

/-- The closure of the extension of a weak ideal of definition along a continuous
taut homomorphism is a weak ideal of definition. -/
theorem map_closure_of_isTaut {A : Type u} {B : Type v}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    {φ : A →+* B} (hcont : Continuous φ) (htaut : φ.IsTaut) {I : Ideal A}
    (hI : IsWeakIdealOfDefinition I) :
    IsWeakIdealOfDefinition (Ideal.map φ I).closure := sorry

end TopologicalRing.Ideal.IsWeakIdealOfDefinition

namespace RingHom.IsTaut

/-- A continuous taut homomorphism carries a weakly pre-admissible source ring to
a weakly pre-admissible target ring. -/
theorem isWeaklyPreadmissibleRing {A : Type u} {B : Type v}
    [CommRing A] [TopologicalSpace A] [TopologicalRing.IsWeaklyPreadmissibleRing A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    {φ : A →+* B} (hcont : Continuous φ) (htaut : φ.IsTaut) :
    TopologicalRing.IsWeaklyPreadmissibleRing B := sorry

end RingHom.IsTaut
