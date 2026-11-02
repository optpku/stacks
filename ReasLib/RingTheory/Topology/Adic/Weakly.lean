/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Algebra.LinearTopology
public import Mathlib.Topology.Algebra.Ring.Ideal
public import ReasLib.RingTheory.Topology.Adic.Complete

/-!
# Weakly pre-adic and weakly adic rings
-/

@[expose] public section

universe u

namespace TopologicalRing

section

variable {R : Type u} [CommRing R] [TopologicalSpace R]

namespace Ideal

/-- An ideal is weakly adic when the closures of its powers are open and form a
fundamental system of neighborhoods of `0`. -/
def IsWeaklyAdic [IsTopologicalRing R] (I : Ideal R) : Prop :=
  (∀ n : ℕ, IsOpen ((I ^ n).closure : Set R)) ∧
    (nhds (0 : R)).HasBasis (fun _ : ℕ ↦ True) (fun n ↦ ((I ^ n).closure : Set R))

/-- An ideal is weakly adic if and only if the closures of its powers are open and
cofinal among neighborhoods of `0`. -/
theorem isWeaklyAdic_iff [IsTopologicalRing R] (I : Ideal R) :
    IsWeaklyAdic I ↔
      (∀ n : ℕ, IsOpen ((I ^ n).closure : Set R)) ∧
        ∀ U ∈ nhds (0 : R), ∃ n : ℕ, ((I ^ n).closure : Set R) ⊆ U :=
  by
    constructor
    · rintro ⟨hopen, hbasis⟩
      refine ⟨hopen, fun U hU ↦ ?_⟩
      obtain ⟨n, _, hn⟩ := hbasis.mem_iff.mp hU
      exact ⟨n, hn⟩
    · rintro ⟨hopen, hcofinal⟩
      refine ⟨hopen, ⟨fun U ↦ ⟨?_, ?_⟩⟩⟩
      · intro hU
        obtain ⟨n, hn⟩ := hcofinal U hU
        exact ⟨n, trivial, hn⟩
      · rintro ⟨n, _, hn⟩
        exact Filter.mem_of_superset ((hopen n).mem_nhds (I ^ n).closure.zero_mem) hn

/-- An ideal inducing the ambient adic topology is weakly adic. -/
theorem isWeaklyAdic_of_isAdic [IsTopologicalRing R] {I : Ideal R} (hI : IsAdic I) :
    IsWeaklyAdic I :=
  by
    have hopen := (isAdic_iff.mp hI).1
    have hclosure : ∀ n : ℕ, (I ^ n).closure = I ^ n := fun n ↦
      (I ^ n).closure_eq_of_isClosed
        ((I ^ n).toAddSubgroup.isClosed_of_isOpen (hopen n))
    refine ⟨?_, ?_⟩
    · intro n
      rw [hclosure n]
      exact hopen n
    · simpa only [hclosure] using hI.hasBasis_nhds_zero

end Ideal

/-- A weakly pre-adic ring is a linearly topologized topological ring for which some
ideal is weakly adic. -/
class IsWeaklyPreadicRing (R : Type u) [CommRing R] [TopologicalSpace R] : Prop
    extends IsTopologicalRing R, IsLinearTopology R R where
  /-- A weakly pre-adic ring has a weakly adic ideal. -/
  exists_ideal_isWeaklyAdic : ∃ I : Ideal R, Ideal.IsWeaklyAdic I

/-- A pre-adic ring is weakly pre-adic. -/
instance instIsWeaklyPreadicRing [IsPreadicRing R] : IsWeaklyPreadicRing R := by
  obtain ⟨I, hI⟩ := IsPreadicRing.exists_ideal_isAdic (R := R)
  exact
    { toIsLinearTopology := IsLinearTopology.mk_of_hasBasis R hI.hasBasis_nhds_zero
      exists_ideal_isWeaklyAdic := ⟨I, Ideal.isWeaklyAdic_of_isAdic hI⟩ }

/-- A linearly topologized topological ring is weakly pre-adic exactly when some
ideal is weakly adic. -/
theorem isWeaklyPreadicRing_iff [IsTopologicalRing R] [IsLinearTopology R R] :
    IsWeaklyPreadicRing R ↔ ∃ I : Ideal R, Ideal.IsWeaklyAdic I := by
  exact ⟨fun h ↦ h.exists_ideal_isWeaklyAdic,
    fun h ↦ { exists_ideal_isWeaklyAdic := h }⟩

/-- A linearly topologized ring is weakly pre-adic if and only if some ideal has the
closures of its powers open and cofinal among open ideals. -/
theorem isWeaklyPreadicRing_iff_exists_closure_pow
    [IsTopologicalRing R] [IsLinearTopology R R] :
    IsWeaklyPreadicRing R ↔
      ∃ I : Ideal R,
        (∀ n : ℕ, IsOpen ((I ^ n).closure : Set R)) ∧
          ∀ J : Ideal R, IsOpen (J : Set R) → ∃ n : ℕ, (I ^ n).closure ≤ J :=
  by
    rw [isWeaklyPreadicRing_iff]
    constructor
    · rintro ⟨I, hI⟩
      refine ⟨I, hI.1, fun J hJ ↦ ?_⟩
      obtain ⟨n, _, hn⟩ := hI.2.mem_iff.mp (hJ.mem_nhds J.zero_mem)
      exact ⟨n, hn⟩
    · rintro ⟨I, hopen, hcofinal⟩
      refine ⟨I, (Ideal.isWeaklyAdic_iff I).mpr ⟨hopen, fun U hU ↦ ?_⟩⟩
      obtain ⟨J, hJ, hJU⟩ :=
        (IsLinearTopology.hasBasis_open_ideal (R := R)).mem_iff.mp hU
      obtain ⟨n, hn⟩ := hcofinal J hJ
      exact ⟨n, Set.Subset.trans hn hJU⟩

/-- A weakly adic ring is a complete separated weakly pre-adic ring. -/
class IsWeaklyAdicRing (R : Type u) [CommRing R] [TopologicalSpace R] : Prop
    extends IsWeaklyPreadicRing R where
  /-- The ambient topology is separated. -/
  isT2 : T2Space R
  /-- The ambient additive uniformity is complete. -/
  isComplete : @CompleteSpace R (IsTopologicalAddGroup.rightUniformSpace R)

/-- An adic ring is weakly adic. -/
instance instIsWeaklyAdicRing [IsAdicRing R] : IsWeaklyAdicRing R := by
  obtain ⟨I, hI, _⟩ := IsAdicRing.exists_ideal_isAdicComplete (R := R)
  letI : IsPreadicRing R :=
    { toIsTopologicalRing := IsAdicRing.toIsTopologicalRing
      exists_ideal_isAdic := ⟨I, hI⟩ }
  exact
    { toIsWeaklyPreadicRing := instIsWeaklyPreadicRing
      isT2 := instT2SpaceOfIsAdicRing
      isComplete := instCompleteSpaceOfIsAdicRing }

/-- A weakly adic ring is separated. -/
instance instT2SpaceOfIsWeaklyAdicRing [h : IsWeaklyAdicRing R] : T2Space R :=
  h.isT2

/-- A weakly adic ring is complete for its additive uniformity. -/
instance instCompleteSpaceOfIsWeaklyAdicRing [h : IsWeaklyAdicRing R] :
    @CompleteSpace R (IsTopologicalAddGroup.rightUniformSpace R) := h.isComplete

/-- A weakly pre-adic ring is weakly adic exactly when it is separated and complete
for the additive uniformity. -/
theorem isWeaklyAdicRing_iff [IsWeaklyPreadicRing R] :
    IsWeaklyAdicRing R ↔
      T2Space R ∧ @CompleteSpace R (IsTopologicalAddGroup.rightUniformSpace R) :=
  by
    constructor
    · intro h
      exact ⟨h.isT2, h.isComplete⟩
    · rintro ⟨hT2, hcomplete⟩
      exact { isT2 := hT2, isComplete := hcomplete }

end

end TopologicalRing
