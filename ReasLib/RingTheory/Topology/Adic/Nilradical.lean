module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Topology.Algebra.TopologicallyNilpotent
public import ReasLib.RingTheory.Topology.Adic.Complete
public import ReasLib.RingTheory.Topology.TopologicalNilradical

/-!
# Topological nilradicals of adic rings
-/

@[expose] public section

universe u v

namespace RingHom

/-- The homomorphism on quotients by topological nilradicals induced by a
continuous homomorphism of adic rings. -/
def topologicalNilradicalQuotient {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalRing.IsAdicRing A] [TopologicalRing.IsAdicRing B]
    (φ : A →+* B) (hφ : Continuous φ) :
    A ⧸ topologicalNilradical A →+* B ⧸ topologicalNilradical B :=
  Ideal.quotientMap (topologicalNilradical B) φ (topologicalNilradical.map_le φ hφ)

/-- The map on quotients by topological nilradicals sends the class of `x`
to the class of its image. -/
theorem topologicalNilradicalQuotient_apply {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalRing.IsAdicRing A] [TopologicalRing.IsAdicRing B]
    (φ : A →+* B) (hφ : Continuous φ) (x : A) :
    φ.topologicalNilradicalQuotient hφ (Ideal.Quotient.mk (topologicalNilradical A) x) =
      Ideal.Quotient.mk (topologicalNilradical B) (φ x) :=
  sorry

end RingHom
