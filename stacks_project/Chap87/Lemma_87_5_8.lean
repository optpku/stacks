module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Definition_87_4_8_WeaklyAdmissible
public import stacks_project.Chap87.Definition_87_5_1_Taut

/-!
# Lemma 87.5.8

A continuous taut homomorphism of linearly topologized rings sends a
weakly pre-admissible source to a weakly pre-admissible target.
-/

@[expose] public section

universe u v

open TopologicalRing

namespace RingHom.IsTaut

/-- Lemma 87.5.8: Let `φ : A →+* B` be a continuous homomorphism of linearly
topologized rings. If `φ` is taut and `A` is weakly pre-admissible, then `B` is
weakly pre-admissible. -/
@[stacks 0GX7]
theorem isWeaklyPreadmissibleRing {A : Type u} {B : Type v}
    [CommRing A] [TopologicalSpace A] [IsWeaklyPreadmissibleRing A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    {φ : A →+* B} (hcont : Continuous φ) (htaut : φ.IsTaut) :
    IsWeaklyPreadmissibleRing B :=
  sorry

/-- If `I` is a weak ideal of definition of `A` and `φ` is a continuous taut
homomorphism, then the closure of `Ideal.map φ I` is a weak ideal of definition of
`B`. -/
theorem isWeakIdealOfDefinition_closure_map {A : Type u} {B : Type v}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    {φ : A →+* B} (hcont : Continuous φ) (htaut : φ.IsTaut) {I : Ideal A}
    (hI : TopologicalRing.Ideal.IsWeakIdealOfDefinition I) :
    TopologicalRing.Ideal.IsWeakIdealOfDefinition (Ideal.map φ I).closure :=
  sorry

end RingHom.IsTaut
