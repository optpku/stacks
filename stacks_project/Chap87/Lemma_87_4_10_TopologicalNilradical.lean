/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Topology.TopologicalNilradical

/-!
# Topological nilradical API

The shared topological nilradical API provides closedness, radicality,
closure characterizations, and containment under continuous ring homomorphisms.
-/

@[expose] public section

universe u v

#check (topologicalNilradical.isClosed :
  ∀ {R : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLinearTopology R R], IsClosed (topologicalNilradical R : Set R))

#check (@topologicalNilradical.isRadical :
  ∀ {R : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLinearTopology R R], (topologicalNilradical R).IsRadical)

#check (topologicalNilradical.closure_eq :
  ∀ {R : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLinearTopology R R], (topologicalNilradical R).closure = topologicalNilradical R)

#check (topologicalNilradical.radical_eq :
  ∀ {R : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLinearTopology R R], (topologicalNilradical R).radical = topologicalNilradical R)

#check (topologicalNilradical.map_le :
  ∀ {A : Type u} {B : Type v}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    (φ : A →+* B), Continuous φ →
    topologicalNilradical A ≤ (topologicalNilradical B).comap φ)

#check (topologicalNilradical.closure_span_image_le :
  ∀ {A : Type u} {B : Type v}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    (φ : A →+* B), Continuous φ → ∀ {s : Set A},
    s ⊆ topologicalNilradical A →
    (Ideal.span (φ '' s)).closure ≤ topologicalNilradical B)

#check (topologicalNilradical.closure_map_le :
  ∀ {A : Type u} {B : Type v}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    (φ : A →+* B), Continuous φ → ∀ {I : Ideal A},
    I ≤ topologicalNilradical A → (I.map φ).closure ≤ topologicalNilradical B)

#check (topologicalNilradical.mem_closure_span_image :
  ∀ {A : Type u} {B : Type v}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    (φ : A →+* B), Continuous φ → ∀ {s : Set A},
    s ⊆ topologicalNilradical A → ∀ {x : B},
    x ∈ (Ideal.span (φ '' s)).closure → IsTopologicallyNilpotent x)
