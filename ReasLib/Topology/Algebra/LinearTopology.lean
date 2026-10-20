/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Group.Pointwise.Set.Scalar
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.Topology.Algebra.LinearTopology
public import Mathlib.Topology.Algebra.Module.Basic

/-!
# Continuity criteria for linearly topologized modules
-/

@[expose] public section

open scoped Pointwise

universe u v

namespace IsLinearTopology

/-- Addition is continuous on a linearly topologized module when translations are continuous. -/
theorem continuousAdd {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    [TopologicalSpace M] [IsLinearTopology R M] [ContinuousConstVAdd M M] :
    Continuous fun p : M × M ↦ p.1 + p.2 := sorry

/-- Scalar multiplication is continuous exactly when scalar and module cosets absorb a target
neighbourhood. -/
theorem continuousSMul_iff_exists_vadd_smul_subset {R : Type u} {M : Type v}
    [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [IsLinearTopology R R]
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [IsLinearTopology R M] :
    Continuous (fun p : R × M ↦ p.1 • p.2) ↔
      ∀ (f : R) (x : M) (N : Submodule R M), IsOpen (N : Set M) →
        ∃ (I : Ideal R) (N' : Submodule R M),
          IsOpen (I : Set R) ∧ IsOpen (N' : Set M) ∧
            (f +ᵥ (I : Set R)) • (x +ᵥ (N' : Set M)) ⊆ (f • x) +ᵥ (N : Set M) := sorry

/-- Scalar multiplication is continuous exactly when every vector is pointwise absorbed by open
ideals into every open submodule. -/
theorem continuousSMul_iff_exists_ideal_smul_mem {R : Type u} {M : Type v}
    [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [IsLinearTopology R R]
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [IsLinearTopology R M] :
    Continuous (fun p : R × M ↦ p.1 • p.2) ↔
      ∀ (x : M) (N : Submodule R M), IsOpen (N : Set M) →
        ∃ I : Ideal R, IsOpen (I : Set R) ∧ ∀ r ∈ I, r • x ∈ N := sorry

/-- A continuous homomorphism of linearly topologized commutative rings maps some open ideal into
every prescribed open ideal. -/
theorem exists_open_ideal_map_le {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [TopologicalSpace R] [TopologicalSpace S] [IsTopologicalRing R] [IsTopologicalRing S]
    [IsLinearTopology R R] [IsLinearTopology S S] (φ : R →+* S) (hφ : Continuous φ)
    (J : Ideal S) (hJ : IsOpen (J : Set S)) :
    ∃ I : Ideal R, IsOpen (I : Set R) ∧ I.map φ ≤ J := sorry

end IsLinearTopology
