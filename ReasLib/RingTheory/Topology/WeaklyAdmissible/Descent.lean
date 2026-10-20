module

public import ReasLib.RingTheory.Topology.WeaklyAdmissible
public import ReasLib.Topology.Algebra.Ring.Taut
public import ReasLib.Topology.Algebra.Ring.FaithfullyFlatOpenQuotients
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Descent of weak pre-admissibility

Weak ideals of definition and weak pre-admissibility descend along continuous
taut homomorphisms of linearly topologized rings with faithfully flat open quotients.
-/

@[expose] public section

universe u v

open RingHom

namespace TopologicalRing.IsWeaklyPreadmissibleRing

/-- For a continuous taut homomorphism with faithfully flat open quotients, an
open source ideal whose extension lies in a weak ideal of definition of the
weakly pre-admissible target is itself a weak ideal of definition. -/
theorem isWeakIdealOfDefinition_of {A : Type u} {B : Type v}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [CommRing B] [TopologicalSpace B] [IsWeaklyPreadmissibleRing B] {φ : A →+* B}
    (hcont : Continuous φ) (htaut : φ.IsTaut) (hff : φ.FaithfullyFlatOpenQuotients)
    {J : Ideal B} (hJ : TopologicalRing.Ideal.IsWeakIdealOfDefinition J) {I : Ideal A}
    (hI : IsOpen (I : Set A)) (hmap : Ideal.map φ I ≤ J) :
    TopologicalRing.Ideal.IsWeakIdealOfDefinition I :=
  sorry

/-- Weak pre-admissibility descends along a continuous taut homomorphism of
linearly topologized rings with faithfully flat open quotients. -/
@[stacks 0GXM]
theorem of_isTaut {A : Type u} {B : Type v}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [CommRing B] [TopologicalSpace B] [IsWeaklyPreadmissibleRing B] {φ : A →+* B}
    (hcont : Continuous φ) (htaut : φ.IsTaut) (hff : φ.FaithfullyFlatOpenQuotients) :
    IsWeaklyPreadmissibleRing A :=
  sorry

end TopologicalRing.IsWeaklyPreadmissibleRing
