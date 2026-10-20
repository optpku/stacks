module

public import ReasLib.RingTheory.Topology.Adic.Weakly.Characterization
public import ReasLib.RingTheory.Topology.Adic.Descent

/-!
# Descent of weak pre-adicity

Weak pre-adicity descends along continuous taut homomorphisms of linearly
topologized rings with faithfully flat open quotients.
-/

@[expose] public section

universe u v

open RingHom

namespace TopologicalRing.IsWeaklyPreadicRing

/-- Weak pre-adicity descends along a continuous taut homomorphism of linearly
topologized rings whose canonical quotients by open ideals and the closures of
their extensions are faithfully flat. -/
@[stacks 0GXP]
theorem of_faithfullyFlatOpenQuotients {A : Type u} {B : Type v}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [CommRing B] [TopologicalSpace B] [IsWeaklyPreadicRing B] {φ : A →+* B}
    (hcont : Continuous φ) (htaut : φ.IsTaut) (hff : φ.FaithfullyFlatOpenQuotients) :
    IsWeaklyPreadicRing A :=
  sorry

end TopologicalRing.IsWeaklyPreadicRing
