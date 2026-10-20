/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Topology.FiniteType.Reduction

/-!
# Finite type on reductions of weakly admissible rings

A homomorphism of weakly admissible rings is of finite type on reduction when
the induced map on quotients by topological nilradicals is of finite type.
-/

@[expose] public section

universe u

open TopologicalRing

variable {A B : Type u} [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A]
  [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B]

#check (RingHom.IsFiniteTypeOnReduction : (A →+* B) → Prop)

#check (RingHom.isFiniteTypeOnReduction_iff :
  ∀ (φ : A →+* B) (hφ : Continuous φ),
    φ.IsFiniteTypeOnReduction ↔
      (Ideal.quotientMap (topologicalNilradical B) φ
        (topologicalNilradical.map_le φ hφ)).FiniteType)

#check (RingHom.IsFiniteTypeOnReduction.finiteType :
  ∀ {φ : A →+* B}, φ.IsFiniteTypeOnReduction →
    ∀ (h_le : topologicalNilradical A ≤ (topologicalNilradical B).comap φ),
      (Ideal.quotientMap (topologicalNilradical B) φ h_le).FiniteType)
