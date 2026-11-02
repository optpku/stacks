/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Order.Filter.CountablyGenerated
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.Topology.Algebra.LinearTopology
public import Mathlib.Topology.Algebra.Ring.Ideal

/-!
# Taut homomorphisms of linearly topologized rings

A continuous homomorphism of linearly topologized rings is taut when the closures of the
extensions of open ideals of the source form a fundamental system of open ideals of the target.
-/

@[expose] public section

open scoped Topology

universe u v w

namespace RingHom

/-- A homomorphism of linearly topologized rings is taut if the closures of the
extensions of open ideals of the source form a fundamental system of neighborhoods
of `0` in the target. -/
def IsTaut {A : Type u} {B : Type v}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    (φ : A →+* B) : Prop :=
  (nhds (0 : B)).HasBasis (fun I : Ideal A ↦ IsOpen (I : Set A))
    (fun I ↦ ((Ideal.map φ I).closure : Set B))

variable {A : Type u} {B : Type v}
variable [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
variable [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
variable {C : Type w}
variable [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]

/-- A homomorphism of linearly topologized rings is taut if and only if, for every
open ideal of the source, the closure of its extension is open in the target, and
these closures are cofinal among open ideals of the target. -/
theorem isTaut_iff (φ : A →+* B) :
    φ.IsTaut ↔
      (∀ I : Ideal A, IsOpen (I : Set A) → IsOpen ((Ideal.map φ I).closure : Set B)) ∧
        ∀ J : Ideal B, IsOpen (J : Set B) →
          ∃ I : Ideal A, IsOpen (I : Set A) ∧ (Ideal.map φ I).closure ≤ J := by
  constructor
  · intro hφ
    refine ⟨?_, ?_⟩
    · intro I hI
      exact (Ideal.map φ I).closure.toAddSubgroup.isOpen_of_mem_nhds
        (hφ.mem_of_mem hI)
    · intro J hJ
      exact hφ.mem_iff.mp (hJ.mem_nhds J.zero_mem)
  · rintro ⟨hopen, hcofinal⟩
    exact (IsLinearTopology.hasBasis_open_ideal (R := B)).to_hasBasis'
      (fun J hJ ↦ hcofinal J hJ)
      (fun I hI ↦ (hopen I hI).mem_nhds (Ideal.zero_mem _))

namespace IsTaut

/-- If `φ` is taut, then the closure of the extension of every open ideal of the
source is open in the target. -/
theorem isOpen_closure_map {φ : A →+* B} (hφ : φ.IsTaut) {I : Ideal A}
    (hI : IsOpen (I : Set A)) : IsOpen ((Ideal.map φ I).closure : Set B) :=
  ((isTaut_iff φ).mp hφ).1 I hI

/-- If `φ` is taut, then every open ideal of the target contains the closure of the
extension of some open ideal of the source. -/
theorem exists_closure_map_le {φ : A →+* B} (hφ : φ.IsTaut) {J : Ideal B}
    (hJ : IsOpen (J : Set B)) :
    ∃ I : Ideal A, IsOpen (I : Set A) ∧ (Ideal.map φ I).closure ≤ J :=
  ((isTaut_iff φ).mp hφ).2 J hJ

/-- If a composite of continuous homomorphisms of linearly topologized rings is taut,
then the second homomorphism is taut. -/
theorem of_comp {φ : A →+* B} {ψ : B →+* C} (hφ_cont : Continuous φ)
    (hψ_cont : Continuous ψ) (h : (ψ.comp φ).IsTaut) : ψ.IsTaut := by
  apply (isTaut_iff ψ).mpr
  constructor
  · intro J hJ
    have hmap : Ideal.map (ψ.comp φ) (Ideal.comap φ J) ≤ Ideal.map ψ J := by
      rw [← Ideal.map_map]
      exact Ideal.map_mono (Ideal.map_le_iff_le_comap.mpr le_rfl)
    exact (Ideal.map ψ J).closure.toAddSubgroup.isOpen_of_mem_nhds
      (Filter.mem_of_superset
        ((h.isOpen_closure_map (hJ.preimage hφ_cont)).mem_nhds (Ideal.zero_mem _))
        (closure_mono (SetLike.coe_subset_coe.mpr hmap)))
  · intro K hK
    refine ⟨Ideal.comap ψ K, hK.preimage hψ_cont, ?_⟩
    exact closure_minimal
      (SetLike.coe_subset_coe.mpr (Ideal.map_le_iff_le_comap.mpr le_rfl))
      (K.toAddSubgroup.isClosed_of_isOpen hK)

/-- The composite of two continuous taut homomorphisms of linearly topologized rings
is taut. -/
theorem comp {φ : A →+* B} {ψ : B →+* C} (hφ_cont : Continuous φ)
    (hψ_cont : Continuous ψ) (hφ : φ.IsTaut) (hψ : ψ.IsTaut) :
    (ψ.comp φ).IsTaut := by
  have hclosure (J : Ideal B) :
      (Ideal.map ψ J.closure).closure = (Ideal.map ψ J).closure := by
    apply le_antisymm
    · change closure (Ideal.map ψ J.closure : Set C) ⊆ closure (Ideal.map ψ J : Set C)
      have hmap : Ideal.map ψ J.closure ≤ (Ideal.map ψ J).closure := by
        rw [Ideal.map_le_iff_le_comap]
        intro x hx
        exact map_mem_closure hψ_cont hx (fun _ hy ↦ Ideal.mem_map_of_mem ψ hy)
      exact closure_minimal (SetLike.coe_subset_coe.mpr hmap) isClosed_closure
    · change closure (Ideal.map ψ J : Set C) ⊆ closure (Ideal.map ψ J.closure : Set C)
      have hsub : J ≤ J.closure := subset_closure
      exact closure_mono (SetLike.coe_subset_coe.mpr (Ideal.map_mono hsub))
  apply (isTaut_iff (ψ.comp φ)).mpr
  constructor
  · intro I hI
    have hopen := hψ.isOpen_closure_map (hφ.isOpen_closure_map hI)
    rwa [hclosure, Ideal.map_map] at hopen
  · intro K hK
    obtain ⟨J, hJ, hJK⟩ := hψ.exists_closure_map_le hK
    obtain ⟨I, hI, hIJ⟩ := hφ.exists_closure_map_le hJ
    refine ⟨I, hI, ?_⟩
    have hsub : Ideal.map φ I ≤ (Ideal.map φ I).closure := subset_closure
    have hmap : Ideal.map ψ (Ideal.map φ I) ≤ Ideal.map ψ J :=
      Ideal.map_mono (hsub.trans hIJ)
    rw [← Ideal.map_map]
    exact (closure_mono (SetLike.coe_subset_coe.mpr hmap)).trans hJK

/-- A continuous taut homomorphism of linearly topologized rings transfers a
countable fundamental system of open ideals from the source to the target. -/
theorem isCountablyGenerated_nhds {φ : A →+* B} (hcont : Continuous φ) (htaut : φ.IsTaut)
    [(nhds (0 : A)).IsCountablyGenerated] :
    (nhds (0 : B)).IsCountablyGenerated := by
  obtain ⟨I, hIopen, hI⟩ :=
    (IsLinearTopology.hasBasis_open_ideal (R := A)).exists_antitone_subbasis
  have hb : (nhds (0 : B)).HasBasis (fun _ : ℕ ↦ True)
      (fun n ↦ ((Ideal.map φ (I n)).closure : Set B)) := by
    apply htaut.to_hasBasis
    · intro J hJ
      obtain ⟨n, hn⟩ := hI.mem_iff.mp (hJ.mem_nhds J.zero_mem)
      exact ⟨n, trivial, closure_mono
        (SetLike.coe_subset_coe.mpr (Ideal.map_mono (SetLike.coe_subset_coe.mp hn)))⟩
    · intro n _
      exact ⟨I n, hIopen n, Set.Subset.rfl⟩
  exact hb.isCountablyGenerated

end IsTaut

/-- If `I` is a fundamental system of open ideals of `A`, then `φ` is taut if and
only if the closures of the extensions `Ideal.map φ (I i)` are open and form a
fundamental system of neighborhoods of `0` in `B`. -/
theorem isTaut_iff_hasBasis {ι : Type w} {I : ι → Ideal A}
    (hI : (nhds (0 : A)).HasBasis (fun _ ↦ True) (fun i ↦ (I i : Set A)))
    (hIopen : ∀ i, IsOpen (I i : Set A)) (φ : A →+* B) :
    φ.IsTaut ↔
      (∀ i, IsOpen ((Ideal.map φ (I i)).closure : Set B)) ∧
        (nhds (0 : B)).HasBasis (fun _ ↦ True)
          (fun i ↦ ((Ideal.map φ (I i)).closure : Set B)) := by
  constructor
  · intro hφ
    refine ⟨fun i ↦ hφ.isOpen_closure_map (hIopen i), ?_⟩
    apply hφ.to_hasBasis
    · intro J hJ
      obtain ⟨i, _, hi⟩ := hI.mem_iff.mp (hJ.mem_nhds J.zero_mem)
      exact ⟨i, trivial, closure_mono
        (SetLike.coe_subset_coe.mpr (Ideal.map_mono (SetLike.coe_subset_coe.mp hi)))⟩
    · intro i _
      exact ⟨I i, hIopen i, Set.Subset.rfl⟩
  · rintro ⟨_, hb⟩
    apply hb.to_hasBasis
    · intro i _
      exact ⟨I i, hIopen i, Set.Subset.rfl⟩
    · intro J hJ
      obtain ⟨i, _, hi⟩ := hI.mem_iff.mp (hJ.mem_nhds J.zero_mem)
      exact ⟨i, trivial, closure_mono
        (SetLike.coe_subset_coe.mpr (Ideal.map_mono (SetLike.coe_subset_coe.mp hi)))⟩

end RingHom
