module

public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.Topology.Algebra.Ring.Ideal
public import Mathlib.Topology.Algebra.TopologicallyNilpotent

/-!
# Closedness, radicality, and functoriality of the topological nilradical

In a linearly topologized ring the topological nilradical is a closed radical
ideal. Continuous ring homomorphisms send it into the topological nilradical of
the target, and the closure of an extended image ideal of topologically
nilpotent elements remains contained in the topological nilradical.
-/

@[expose] public section

universe u v w

namespace topologicalNilradical

/-- The topological nilradical of a linearly topologized ring is a closed subset. -/
instance isClosed {R : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLinearTopology R R] : IsClosed (topologicalNilradical R : Set R) := sorry

section

variable {R : Type u}
  [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [IsLinearTopology R R]

/-- The topological nilradical of a linearly topologized ring is a radical ideal. -/
theorem isRadical : (topologicalNilradical R).IsRadical := sorry

/-- The topological nilradical of a linearly topologized ring equals its
topological closure as an ideal. -/
theorem closure_eq : (topologicalNilradical R).closure = topologicalNilradical R := sorry

/-- The topological nilradical of a linearly topologized ring equals its radical. -/
theorem radical_eq : (topologicalNilradical R).radical = topologicalNilradical R := sorry

end

/-- A continuous morphism of monoids with zero sends topologically nilpotent
elements to topologically nilpotent elements. -/
theorem map_isTopologicallyNilpotent {R : Type u} {S : Type v}
    [TopologicalSpace R] [MonoidWithZero R] [MonoidWithZero S] [TopologicalSpace S]
    {F : Type w} [FunLike F R S] [MonoidWithZeroHomClass F R S]
    {φ : F} (hφ : Continuous φ) {a : R} (ha : IsTopologicallyNilpotent a) :
    IsTopologicallyNilpotent (φ a) := sorry

section

variable {A : Type u} {B : Type v}
  [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
  [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]

/-- A continuous ring homomorphism of linearly topologized rings sends the
topological nilradical of the source into the topological nilradical of the
target. -/
theorem map_le (φ : A →+* B) (hφ : Continuous φ) :
    topologicalNilradical A ≤ (topologicalNilradical B).comap φ := sorry

/-- If a subset consists of topologically nilpotent elements, then the closure of
the extended image ideal along a continuous homomorphism of linearly topologized
rings is contained in the topological nilradical of the target. -/
theorem closure_span_image_le (φ : A →+* B) (hφ : Continuous φ) {s : Set A}
    (hs : s ⊆ topologicalNilradical A) :
    (Ideal.span (φ '' s)).closure ≤ topologicalNilradical B := sorry

/-- If an ideal is contained in the topological nilradical, then the closure of
its extension along a continuous homomorphism of linearly topologized rings is
contained in the topological nilradical of the target. -/
theorem closure_map_le (φ : A →+* B) (hφ : Continuous φ) {I : Ideal A}
    (hI : I ≤ topologicalNilradical A) :
    (I.map φ).closure ≤ topologicalNilradical B := sorry

/-- Membership in the closure of the extended image of a set of topologically
nilpotent elements implies topological nilpotence. -/
theorem mem_closure_span_image (φ : A →+* B) (hφ : Continuous φ) {s : Set A}
    (hs : s ⊆ topologicalNilradical A) {x : B}
    (hx : x ∈ (Ideal.span (φ '' s)).closure) : IsTopologicallyNilpotent x := sorry

end

end topologicalNilradical
