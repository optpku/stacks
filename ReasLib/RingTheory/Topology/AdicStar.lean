/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Data.Finite.Defs
public import ReasLib.RingTheory.Topology.Adic.Complete
public import ReasLib.RingTheory.Topology.CountablyIndexed
public import ReasLib.RingTheory.Topology.WeakIdealCompletion.Properties
import Mathlib.RingTheory.Finiteness.Basic

/-!
# Adic rings with a finitely generated ideal of definition

Objects of `WAdm^{adic*}` are complete separated adic rings that admit a
finitely generated ideal of definition. Finite products, countable indexing,
and weak-ideal completions stay in this class, so locality squares for
morphisms of `WAdm^{adic*}` can reuse `LocalizeSquare`.
-/

@[expose] public section

universe u

namespace TopologicalRing

/-- A complete separated adic ring admitting a finitely generated ideal of definition. -/
class IsAdicStarRing (R : Type u) [CommRing R] [TopologicalSpace R] : Prop
    extends IsAdicRing R where
  /-- There is a finitely generated ideal of definition. -/
  exists_fg_isIdealOfDefinition :
    ∃ I : Ideal R, I.FG ∧ Ideal.IsIdealOfDefinition I

namespace IsAdicStarRing

variable {R : Type u} [CommRing R] [TopologicalSpace R]

/-- An adic ring is adic-star if it admits a
finitely generated ideal of definition. -/
theorem of [IsAdicRing R]
    (h : ∃ I : Ideal R, I.FG ∧ Ideal.IsIdealOfDefinition I) :
    IsAdicStarRing R where
  toIsAdicRing := inferInstance
  exists_fg_isIdealOfDefinition := h

/-- An adic-star ring is adic and has a finitely generated ideal of
definition. -/
theorem spec [IsAdicStarRing R] :
    IsAdicRing R ∧ ∃ I : Ideal R, I.FG ∧ Ideal.IsIdealOfDefinition I :=
  ⟨inferInstance, exists_fg_isIdealOfDefinition⟩

/-- A topological ring is adic-star if and only if it is adic and has a
finitely generated ideal of definition. -/
theorem iff :
    IsAdicStarRing R ↔
      IsAdicRing R ∧ ∃ I : Ideal R, I.FG ∧ Ideal.IsIdealOfDefinition I := by
  constructor
  · intro h
    exact spec
  · rintro ⟨hR, h⟩
    exact { hR with exists_fg_isIdealOfDefinition := h }

/-- A Noetherian adic ring is adic-star. -/
instance of_isNoetherianRing [IsAdicRing R] [IsNoetherianRing R] :
    IsAdicStarRing R := by
  letI : IsTopologicalRing R := IsAdicRing.toIsTopologicalRing
  obtain ⟨I, hI, _⟩ := IsAdicRing.exists_ideal_isAdicComplete (R := R)
  refine of ⟨I, IsNoetherian.noetherian I, ?_⟩
  exact ⟨by simpa only [pow_one] using (isAdic_iff.mp hI).1 1,
    (isAdic_iff.mp hI).2⟩

/-- An adic-star ring is countably indexed. -/
instance instIsCountablyIndexed [IsAdicStarRing R] : IsCountablyIndexed R := by
  letI : IsTopologicalRing R := IsAdicRing.toIsTopologicalRing
  obtain ⟨I, hI, _⟩ := IsAdicRing.exists_ideal_isAdicComplete (R := R)
  exact ⟨⟨fun n => I ^ n, (isAdic_iff.mp hI).1, hI.hasBasis_nhds_zero⟩⟩

private theorem pi_ideal_pow {ι : Type u} [Finite ι] {A : ι → Type u}
    [∀ i, CommRing (A i)] (I : ∀ i, Ideal (A i)) (n : ℕ) :
    Ideal.pi I ^ n = Ideal.pi (fun i => I i ^ n) := by
  apply Ideal.piOrderIso.injective
  funext i
  change (Ideal.pi I ^ n).map (Pi.evalRingHom A i) =
    (Ideal.pi (fun i => I i ^ n)).map (Pi.evalRingHom A i)
  simp only [Ideal.map_pow, Ideal.map_evalRingHom_pi]

private theorem pi_ideal_fg {ι : Type u} [Finite ι] {A : ι → Type u}
    [∀ i, CommRing (A i)] (I : ∀ i, Ideal (A i)) (hI : ∀ i, (I i).FG) :
    (Ideal.pi I).FG := by
  letI (i : ι) : Algebra (∀ i, A i) (A i) := (Pi.evalRingHom A i).toAlgebra
  have hfg (i : ι) : ((I i).restrictScalars (∀ i, A i)).FG :=
    Submodule.FG.restrictScalars_of_surjective (hI i) (Function.surjective_eval i)
  have heq : (Ideal.pi I : Submodule (∀ i, A i) (∀ i, A i)) =
      Submodule.pi Set.univ (fun i => (I i).restrictScalars (∀ i, A i)) := by
    ext x
    change (∀ i, x i ∈ I i) ↔ (∀ i ∈ (Set.univ : Set ι), x i ∈ I i)
    simp only [Set.mem_univ, forall_const]
  change (Ideal.pi I : Submodule (∀ i, A i) (∀ i, A i)).FG
  rw [heq]
  exact Submodule.fg_pi hfg

private theorem isAdic_pi_ideal {ι : Type u} [Finite ι] {A : ι → Type u}
    [∀ i, CommRing (A i)] [∀ i, TopologicalSpace (A i)]
    [∀ i, IsTopologicalRing (A i)]
    (I : ∀ i, Ideal (A i)) (hI : ∀ i, IsAdic (I i)) : IsAdic (Ideal.pi I) := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  apply isAdic_iff.mpr
  constructor
  · intro n
    rw [pi_ideal_pow]
    change IsOpen {x : ∀ i, A i | ∀ i, x i ∈ I i ^ n}
    simpa only [Set.pi, Set.mem_univ, forall_const, SetLike.mem_coe] using
      (isOpen_set_pi (Set.finite_univ : (Set.univ : Set ι).Finite)
        (fun i _ => (isAdic_iff.mp (hI i)).1 n))
  · intro U hU
    rw [nhds_pi] at hU
    obtain ⟨⟨s, k⟩, _, hsub⟩ :=
      (Filter.hasBasis_pi (fun i => (hI i).hasBasis_nhds_zero)).mem_iff.mp hU
    refine ⟨Finset.univ.sup k, ?_⟩
    rw [pi_ideal_pow]
    intro x hx
    apply hsub
    intro i hi
    exact Ideal.pow_le_pow_right (Finset.le_sup (Finset.mem_univ i)) (hx i)

private theorem isAdic_of_idealOfDefinition [IsAdicRing R] {I : Ideal R}
    (hI : Ideal.IsIdealOfDefinition I) : IsAdic I := by
  letI : IsTopologicalRing R := IsAdicRing.toIsTopologicalRing
  obtain ⟨J, hJ, _⟩ := IsAdicRing.exists_ideal_isAdicComplete (R := R)
  obtain ⟨m, _, hm⟩ := hJ.hasBasis_nhds_zero.mem_iff.mp (hI.1.mem_nhds I.zero_mem)
  refine isAdic_iff.mpr ⟨fun n => ?_, hI.2⟩
  apply (I ^ n).toAddSubgroup.isOpen_of_mem_nhds
  refine Filter.mem_of_superset (hJ.hasBasis_nhds_zero.mem_of_mem (i := m * n) trivial) ?_
  intro x hx
  apply Ideal.pow_right_mono (show J ^ m ≤ I from hm) n
  simpa only [pow_mul, SetLike.mem_coe] using hx

/-- Finite products of adic-star rings are adic-star. -/
instance instPi {ι : Type u} [Finite ι] {A : ι → Type u}
    [∀ i, CommRing (A i)] [∀ i, TopologicalSpace (A i)]
    [∀ i, IsAdicStarRing (A i)] :
    IsAdicStarRing (∀ i, A i) := by
  classical
  letI (i : ι) : IsTopologicalRing (A i) := IsAdicRing.toIsTopologicalRing
  choose I hfg hdef using
    (fun i => exists_fg_isIdealOfDefinition (R := A i))
  have hI (i : ι) : IsAdic (I i) := isAdic_of_idealOfDefinition (hdef i)
  have hPi : IsAdic (Ideal.pi I) := isAdic_pi_ideal I hI
  letI (i : ι) : UniformSpace (A i) := IsTopologicalAddGroup.rightUniformSpace (A i)
  letI (i : ι) : IsUniformAddGroup (A i) := isUniformAddGroup_of_addCommGroup
  letI (i : ι) : CompleteSpace (A i) := by
    obtain ⟨K, hK, hcomplete⟩ := IsAdicRing.exists_ideal_isAdicComplete (R := A i)
    exact hK.isPrecomplete_iff.mp hcomplete.toIsPrecomplete
  letI (i : ι) : T2Space (A i) := by
    obtain ⟨K, hK, hcomplete⟩ := IsAdicRing.exists_ideal_isAdicComplete (R := A i)
    exact hK.isHausdorff_iff.mp hcomplete.toIsHausdorff
  letI : UniformSpace (∀ i, A i) := Pi.uniformSpace _
  refine
    { toIsAdicRing :=
        { toIsTopologicalRing := inferInstance
          exists_ideal_isAdicComplete :=
            ⟨Ideal.pi I, hPi, hPi.isAdicComplete_iff.mpr ⟨inferInstance, inferInstance⟩⟩ }
      exists_fg_isIdealOfDefinition := ⟨Ideal.pi I, pi_ideal_fg I hfg, ?_⟩ }
  exact ⟨by simpa only [pow_one] using (isAdic_iff.mp hPi).1 1,
    (isAdic_iff.mp hPi).2⟩

/-- The weak-ideal completion of an algebra over an adic-star ring is adic-star. -/
instance instWeakIdealCompletion {A A' : Type u}
    [CommRing A] [TopologicalSpace A] [IsAdicStarRing A]
    [CommRing A'] [Algebra A A'] :
    IsAdicStarRing (weakIdealCompletion A A') := sorry

end IsAdicStarRing

end TopologicalRing
