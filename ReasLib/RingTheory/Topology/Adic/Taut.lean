/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Topology.Adic.Basic
public import ReasLib.Topology.Algebra.Ring.Taut

/-!
# Taut homomorphisms and ideals of definition
-/

@[expose] public section

universe u v

open TopologicalRing

namespace RingHom.IsTaut

/-- The closure of the extension of an ideal of definition along a continuous taut
homomorphism is an ideal of definition. -/
theorem isIdealOfDefinition_closure_map {A : Type u} {B : Type v}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    {φ : A →+* B} (hcont : Continuous φ) (htaut : φ.IsTaut) {I : Ideal A}
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) :
    TopologicalRing.Ideal.IsIdealOfDefinition (Ideal.map φ I).closure := sorry

/-- Pre-admissibility ascends along a continuous taut homomorphism of linearly
topologized rings. -/
theorem isPreadmissibleRing {A : Type u} {B : Type v}
    [CommRing A] [TopologicalSpace A] [IsPreadmissibleRing A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    {φ : A →+* B} (hcont : Continuous φ) (htaut : φ.IsTaut) :
    IsPreadmissibleRing B := sorry

end RingHom.IsTaut
