/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import Mathlib.Order.Filter.CountablyGenerated
public import ReasLib.RingTheory.Topology.Adic.Weakly.Taut

/-!
# Taut pre-adic presentations and weak pre-adicity

Weak pre-adicity is characterized by taut pre-adic presentations and by open
closures of powers of ideals of definition.
-/

@[expose] public section

universe u v

open scoped Topology
open TopologicalRing

namespace TopologicalRing

/-- A taut continuous homomorphism to `A` from some pre-adic linearly topologized
ring. -/
structure TautPreadicHom (A : Type u)
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A] where
  /-- Source pre-adic topological ring. -/
  source : Type v
  /-- Commutative ring structure on the source. -/
  [commRing : CommRing source]
  /-- Topology on the source, possibly distinct from any ambient topology on the
  same carrier. -/
  [topologicalSpace : TopologicalSpace source]
  /-- The source is a topological ring. -/
  [isTopologicalRing : IsTopologicalRing source]
  /-- The source is linearly topologized. -/
  [isLinearTopology : IsLinearTopology source source]
  /-- The source is pre-adic. -/
  [isPreadicRing : IsPreadicRing source]
  /-- Underlying ring homomorphism. -/
  toRingHom : source →+* A
  /-- The homomorphism is continuous. -/
  continuous : Continuous toRingHom
  /-- The homomorphism is taut. -/
  isTaut : toRingHom.IsTaut

namespace TautPreadicHom

variable {A : Type u}
variable [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]

/-- Bundle a taut continuous homomorphism from a pre-adic linearly topologized
ring. -/
def of {A' : Type v} [CommRing A'] [TopologicalSpace A'] [IsPreadicRing A']
    [IsLinearTopology A' A'] (φ : A' →+* A) (hcont : Continuous φ) (htaut : φ.IsTaut) :
    TautPreadicHom A where
  source := A'
  toRingHom := φ
  continuous := hcont
  isTaut := htaut

/-- The bundled homomorphism recovers the supplied ring homomorphism. -/
theorem of_toRingHom {A' : Type v} [CommRing A'] [TopologicalSpace A'] [IsPreadicRing A']
    [IsLinearTopology A' A'] (φ : A' →+* A) (hcont : Continuous φ) (htaut : φ.IsTaut) :
    (of φ hcont htaut).toRingHom = φ :=
  rfl

/-- The bundled source recovers the supplied pre-adic ring. -/
theorem of_source {A' : Type v} [CommRing A'] [TopologicalSpace A'] [IsPreadicRing A']
    [IsLinearTopology A' A'] (φ : A' →+* A) (hcont : Continuous φ) (htaut : φ.IsTaut) :
    (of φ hcont htaut).source = A' :=
  rfl

/-- The identity from the adic topology of a weakly adic ideal to the ambient
ring topology is continuous. -/
theorem continuous_adicId {I : Ideal A} (hI : Ideal.IsWeaklyAdic I) :
    @Continuous A A I.adicTopology _ (RingHom.id A) := by
  refine (@continuous_iff_continuousAt A A I.adicTopology _ (RingHom.id A)).mpr fun x => ?_
  have hx := hI.2.map (fun y : A => x + y)
  rw [map_add_left_nhds_zero] at hx
  change Filter.Tendsto (RingHom.id A) (@nhds A I.adicTopology x) (nhds x)
  rw [(I.hasBasis_nhds_adic x).tendsto_iff hx]
  intro n _
  refine ⟨n, trivial, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  exact ⟨y, subset_closure hy, rfl⟩

/-- The identity from the adic topology of a weakly adic ideal to the ambient
linearly topologized ring is taut. -/
theorem isTaut_adicId {I : Ideal A} (hI : Ideal.IsWeaklyAdic I) :
    @RingHom.IsTaut A A _ I.adicTopology
      (Ideal.nonarchimedean I).toIsTopologicalRing (Ideal.isLinearTopology I) _ _ _ _
      (RingHom.id A) := by
  change (nhds (0 : A)).HasBasis
    (fun J : Ideal A => @IsOpen A I.adicTopology (J : Set A))
    (fun J => ((Ideal.map (RingHom.id A) J).closure : Set A))
  refine hI.2.to_hasBasis (fun n _ => ?_) (fun J hJ => ?_)
  · refine ⟨I ^ n, ?_, by simp⟩
    letI := I.adicTopology
    exact (I.openAddSubgroup n).isOpen'
  · have hJn : (J : Set A) ∈ @nhds A I.adicTopology 0 := by
      letI := I.adicTopology
      exact hJ.mem_nhds J.zero_mem
    obtain ⟨n, _, hn⟩ := I.hasBasis_nhds_zero_adic.mem_iff.mp hJn
    exact ⟨n, trivial, by simpa using closure_mono hn⟩

/-- The identity on `A`, viewed from the `I`-adic topology, as a taut pre-adic
presentation when `I` is weakly adic. -/
def ofAdicId {I : Ideal A} (hI : Ideal.IsWeaklyAdic I) : TautPreadicHom A where
  source := A
  topologicalSpace := I.adicTopology
  isTopologicalRing := (Ideal.nonarchimedean I).toIsTopologicalRing
  isLinearTopology := Ideal.isLinearTopology I
  isPreadicRing :=
    @IsPreadicRing.mk A _ I.adicTopology (Ideal.nonarchimedean I).toIsTopologicalRing ⟨I, rfl⟩
  toRingHom := RingHom.id A
  continuous := continuous_adicId hI
  isTaut := isTaut_adicId hI

/-- The `I`-adic identity presentation has source `A`. -/
theorem ofAdicId_source {I : Ideal A} (hI : Ideal.IsWeaklyAdic I) :
    (ofAdicId hI).source = A :=
  rfl

/-- The `I`-adic identity presentation is the identity ring homomorphism. -/
theorem ofAdicId_toRingHom {I : Ideal A} (hI : Ideal.IsWeaklyAdic I) :
    (ofAdicId hI).toRingHom = RingHom.id A :=
  rfl

/-- The `I`-adic identity presentation uses the `I`-adic topology on the source. -/
theorem ofAdicId_topologicalSpace {I : Ideal A} (hI : Ideal.IsWeaklyAdic I) :
    (ofAdicId hI).topologicalSpace = I.adicTopology :=
  rfl

/-- A taut continuous map from a pre-adic ring implies that the target is weakly
pre-adic. -/
theorem isWeaklyPreadicRing (f : TautPreadicHom A) : IsWeaklyPreadicRing A := by
  cases f with
  | mk source toRingHom continuous isTaut =>
    exact IsWeaklyPreadicRing.of_isTaut continuous isTaut

end TautPreadicHom

end TopologicalRing

variable {A : Type u}
variable [CommRing A] [TopologicalSpace A]

namespace TopologicalRing.Ideal

/-- An ideal of definition whose positive powers have open closures is weakly
adic. -/
theorem IsWeaklyAdic.of_isIdealOfDefinition [IsTopologicalRing A] {I : Ideal A}
    (hI : IsIdealOfDefinition I)
    (hopen : ∀ n : ℕ, 1 ≤ n → IsOpen ((I ^ n).closure : Set A)) : IsWeaklyAdic I := by
  have hopen' : ∀ n : ℕ, IsOpen ((I ^ n).closure : Set A) := by
    intro n
    cases n with
    | zero => simp
    | succ n => exact hopen (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
  refine ⟨hopen', ⟨fun U => ⟨fun hU => ?_, ?_⟩⟩⟩
  · obtain ⟨V, hV, hVclosed, hVU⟩ := exists_mem_nhds_isClosed_subset hU
    obtain ⟨n, hn⟩ := hI.2 V hV
    exact ⟨n, trivial, (closure_minimal hn hVclosed).trans hVU⟩
  · rintro ⟨n, _, hn⟩
    exact Filter.mem_of_superset ((hopen' n).mem_nhds (I ^ n).closure.zero_mem) hn

private theorem closure_pow_le [IsTopologicalRing A] (I : Ideal A) (n : ℕ) :
    I.closure ^ n ≤ (I ^ n).closure := by
  induction n with
  | zero =>
    intro x _
    exact subset_closure (by simp)
  | succ n ih =>
    rw [pow_succ, pow_succ]
    refine (mul_le_mul_left ih I.closure).trans ?_
    exact Ideal.mul_le.mpr fun x hx y hy =>
      map_mem_closure₂ continuous_mul hx hy fun a ha b hb => Ideal.mul_mem_mul ha hb

private theorem IsWeaklyAdic.isIdealOfDefinition_closure [IsTopologicalRing A]
    {I : Ideal A} (hI : IsWeaklyAdic I) : IsIdealOfDefinition I.closure := by
  refine ⟨by simpa using hI.1 1, fun U hU => ?_⟩
  obtain ⟨n, _, hn⟩ := hI.2.mem_iff.mp hU
  exact ⟨n, Set.Subset.trans (closure_pow_le I n) hn⟩

private theorem IsWeaklyAdic.isOpen_closure_pow [IsTopologicalRing A]
    {I J : Ideal A} (hI : IsWeaklyAdic I) (hJ : IsIdealOfDefinition J) (n : ℕ) :
    IsOpen ((J ^ n).closure : Set A) := by
  obtain ⟨k, _, hk⟩ := hI.2.mem_iff.mp (hJ.1.mem_nhds J.zero_mem)
  have hle : I ^ k ≤ J := Set.Subset.trans subset_closure hk
  have hpow : I ^ (k * n) ≤ J ^ n := by
    rw [pow_mul]
    exact Ideal.pow_right_mono hle n
  apply (J ^ n).closure.toAddSubgroup.isOpen_of_mem_nhds
  exact Filter.mem_of_superset (hI.2.mem_of_mem (i := k * n) trivial)
    (closure_mono hpow)

end TopologicalRing.Ideal

namespace TopologicalRing

/-- A weakly pre-adic ring is pre-admissible. -/
instance instIsPreadmissibleRing_of_isWeaklyPreadicRing [IsWeaklyPreadicRing A] :
    IsPreadmissibleRing A := by
  obtain ⟨I, hI⟩ := IsWeaklyPreadicRing.exists_ideal_isWeaklyAdic (R := A)
  exact ⟨⟨I.closure, hI.isIdealOfDefinition_closure⟩⟩

namespace IsWeaklyPreadicRing

/-- A linearly topologized ring is weakly pre-adic if and only if it admits a
taut continuous pre-adic presentation, equivalently if it is pre-admissible
and the closures of positive powers of some, or every, ideal of definition
are open. -/
theorem tfae [IsTopologicalRing A] [IsLinearTopology A A] :
    List.TFAE
      [ IsWeaklyPreadicRing A
      , Nonempty (TautPreadicHom.{u, u} A)
      , IsPreadmissibleRing A ∧
          ∃ I : Ideal A, Ideal.IsIdealOfDefinition I ∧
            ∀ n : ℕ, 1 ≤ n → IsOpen ((I ^ n).closure : Set A)
      , IsPreadmissibleRing A ∧
          ∀ I : Ideal A, Ideal.IsIdealOfDefinition I →
            ∀ n : ℕ, 1 ≤ n → IsOpen ((I ^ n).closure : Set A) ] := by
  have h12 : IsWeaklyPreadicRing A ↔ Nonempty (TautPreadicHom.{u, u} A) := by
    constructor
    · intro h
      obtain ⟨I, hI⟩ := h.exists_ideal_isWeaklyAdic
      exact ⟨TautPreadicHom.ofAdicId hI⟩
    · rintro ⟨f⟩
      letI := f.commRing
      letI := f.topologicalSpace
      letI := f.isTopologicalRing
      letI := f.isLinearTopology
      letI := f.isPreadicRing
      obtain ⟨I, hI⟩ := IsPreadicRing.exists_ideal_isAdic (R := f.source)
      have hb : (nhds (0 : A)).HasBasis (fun _ : ℕ => True)
          (fun n => ((Ideal.map f.toRingHom (I ^ n)).closure : Set A)) := by
        refine f.isTaut.to_hasBasis (fun J hJ => ?_) (fun n _ => ?_)
        · obtain ⟨n, _, hn⟩ := hI.hasBasis_nhds_zero.mem_iff.mp (hJ.mem_nhds J.zero_mem)
          exact ⟨n, trivial, closure_mono (Ideal.map_mono hn)⟩
        · exact ⟨I ^ n, (isAdic_iff.mp hI).1 n, Set.Subset.rfl⟩
      have hb' : (nhds (0 : A)).HasBasis (fun _ : ℕ => True)
          (fun n => (((Ideal.map f.toRingHom I) ^ n).closure : Set A)) := by
        simpa only [Ideal.map_pow] using hb
      have hopen : ∀ n : ℕ, IsOpen (((Ideal.map f.toRingHom I) ^ n).closure : Set A) := by
        intro n
        exact ((Ideal.map f.toRingHom I) ^ n).closure.toAddSubgroup.isOpen_of_mem_nhds
          (hb'.mem_of_mem trivial)
      exact ⟨⟨Ideal.map f.toRingHom I, hopen, hb'⟩⟩
  have h13 : IsWeaklyPreadicRing A ↔
      IsPreadmissibleRing A ∧
        ∃ I : Ideal A, Ideal.IsIdealOfDefinition I ∧
          ∀ n : ℕ, 1 ≤ n → IsOpen ((I ^ n).closure : Set A) := by
    constructor
    · intro h
      obtain ⟨I, hI⟩ := h.exists_ideal_isWeaklyAdic
      have hdef := hI.isIdealOfDefinition_closure
      exact ⟨inferInstance, I.closure, hdef, fun n _ => hI.isOpen_closure_pow hdef n⟩
    · rintro ⟨_, I, hI, hopen⟩
      exact ⟨⟨I, Ideal.IsWeaklyAdic.of_isIdealOfDefinition hI hopen⟩⟩
  have h34 : (IsPreadmissibleRing A ∧
      ∃ I : Ideal A, Ideal.IsIdealOfDefinition I ∧
        ∀ n : ℕ, 1 ≤ n → IsOpen ((I ^ n).closure : Set A)) ↔
      (IsPreadmissibleRing A ∧
        ∀ I : Ideal A, Ideal.IsIdealOfDefinition I →
          ∀ n : ℕ, 1 ≤ n → IsOpen ((I ^ n).closure : Set A)) := by
    constructor
    · rintro ⟨h, I, hI, hopen⟩
      have hw := Ideal.IsWeaklyAdic.of_isIdealOfDefinition hI hopen
      exact ⟨h, fun J hJ n _ => hw.isOpen_closure_pow hJ n⟩
    · rintro ⟨h, hopen⟩
      obtain ⟨I, hI⟩ := h.exists_ideal_isIdealOfDefinition
      exact ⟨h, I, hI, hopen I hI⟩
  apply List.tfae_of_forall (IsWeaklyPreadicRing A)
  intro P hP
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
  rcases hP with rfl | rfl | rfl | rfl
  · rfl
  · exact h12.symm
  · exact h13.symm
  · exact (h13.trans h34).symm

/-- A linearly topologized ring is weakly pre-adic if and only if it admits a taut
pre-adic presentation. -/
theorem iff_nonempty_tautPreadicHom [IsTopologicalRing A] [IsLinearTopology A A] :
    IsWeaklyPreadicRing A ↔ Nonempty (TautPreadicHom.{u, u} A) :=
  tfae.out 0 1

/-- A linearly topologized ring is weakly pre-adic if and only if it is
pre-admissible and some ideal of definition has open closures of positive
powers. -/
theorem iff_exists_isIdealOfDefinition [IsTopologicalRing A] [IsLinearTopology A A] :
    IsWeaklyPreadicRing A ↔
      IsPreadmissibleRing A ∧
        ∃ I : Ideal A, Ideal.IsIdealOfDefinition I ∧
          ∀ n : ℕ, 1 ≤ n → IsOpen ((I ^ n).closure : Set A) :=
  tfae.out 0 2

/-- A linearly topologized ring is weakly pre-adic if and only if it is
pre-admissible and every ideal of definition has open closures of positive
powers. -/
theorem iff_forall_isIdealOfDefinition [IsTopologicalRing A] [IsLinearTopology A A] :
    IsWeaklyPreadicRing A ↔
      IsPreadmissibleRing A ∧
        ∀ I : Ideal A, Ideal.IsIdealOfDefinition I →
          ∀ n : ℕ, 1 ≤ n → IsOpen ((I ^ n).closure : Set A) :=
  tfae.out 0 3

end IsWeaklyPreadicRing

/-- A weakly adic ring is admissible. -/
instance instIsAdmissibleRing_of_isWeaklyAdicRing [IsWeaklyAdicRing A] :
    IsAdmissibleRing A where
  toIsPreadmissibleRing := inferInstance
  isT2 := IsWeaklyAdicRing.isT2
  isComplete := IsWeaklyAdicRing.isComplete

/-- A weakly adic ring has a countable fundamental system of open ideals. -/
instance instIsCountablyGenerated_nhds_of_isWeaklyAdicRing [IsWeaklyAdicRing A] :
    (nhds (0 : A)).IsCountablyGenerated := by
  obtain ⟨I, hI⟩ := IsWeaklyPreadicRing.exists_ideal_isWeaklyAdic (R := A)
  exact hI.2.isCountablyGenerated

end TopologicalRing
