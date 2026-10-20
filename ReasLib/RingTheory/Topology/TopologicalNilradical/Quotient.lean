/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import ReasLib.RingTheory.Topology.TopologicalNilradical

/-!
# Maps on quotients by topological nilradicals

Continuous ring homomorphisms of linearly topologized rings induce
homomorphisms on their quotients by the topological nilradicals.
-/

@[expose] public section

noncomputable section

universe u v

namespace topologicalNilradical

variable {A : Type u} {B : Type v}
  [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
  [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]

/-- The homomorphism on quotients by topological nilradicals induced by a
continuous homomorphism of linearly topologized rings. -/
def quotientMap (φ : A →+* B) (hφ : Continuous φ) :
    A ⧸ topologicalNilradical A →+* B ⧸ topologicalNilradical B :=
  Ideal.quotientMap (topologicalNilradical B) φ (topologicalNilradical.map_le φ hφ)

/-- The induced map on topological-nilradical quotients sends the class of an
element to the class of its image. -/
theorem quotientMap_apply (φ : A →+* B) (hφ : Continuous φ) (x : A) :
    quotientMap φ hφ (Ideal.Quotient.mk (topologicalNilradical A) x) =
      Ideal.Quotient.mk (topologicalNilradical B) (φ x) :=
  Ideal.quotientMap_mk

end topologicalNilradical
