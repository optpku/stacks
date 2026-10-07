module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Topology.Adic.Basic
public import stacks_project.Chap87.Definition_87_5_1_Taut

/-!
# Lemma 87.5.9

A continuous taut homomorphism of linearly topologized rings sends a
pre-admissible source to a pre-admissible target.
-/

@[expose] public section

universe u v

open TopologicalRing

namespace RingHom.IsTaut

/-- Lemma 87.5.9: Let `φ : A →+* B` be a continuous homomorphism of linearly
topologized rings. If `φ` is taut and `A` is pre-admissible, then `B` is
pre-admissible. -/
@[stacks 0GX8]
theorem isPreadmissibleRing {A : Type u} {B : Type v}
    [CommRing A] [TopologicalSpace A] [IsPreadmissibleRing A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    {φ : A →+* B} (hcont : Continuous φ) (htaut : φ.IsTaut) :
    IsPreadmissibleRing B :=
  sorry

/-- If `I` is an ideal of definition of `A` and `φ` is a continuous taut
homomorphism, then the closure of `Ideal.map φ I` is an ideal of definition of
`B`. -/
theorem isIdealOfDefinition_closure_map {A : Type u} {B : Type v}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    {φ : A →+* B} (hcont : Continuous φ) (htaut : φ.IsTaut) {I : Ideal A}
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) :
    TopologicalRing.Ideal.IsIdealOfDefinition (Ideal.map φ I).closure :=
  sorry

end RingHom.IsTaut
