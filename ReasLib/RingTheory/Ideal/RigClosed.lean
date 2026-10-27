/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import Mathlib.Order.Minimal
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.Algebra.Ring.Ideal
public import ReasLib.RingTheory.Completion.LocalRing
public import ReasLib.RingTheory.Topology.Adic.Nilradical

/-!
# Rig-closed primes of Noetherian adic rings
-/

@[expose] public section

universe u v

open IsLocalRing

namespace Ideal

/-- A prime of a Noetherian adic ring is rig-closed when its quotient has Krull
dimension one and no ideal of definition is contained in the prime. -/
class IsRigClosed {R : Type u} [CommRing R] [TopologicalSpace R]
    [TopologicalRing.IsAdicRing R] [IsNoetherianRing R] (q : Ideal R) : Prop where
  /-- A rig-closed ideal is prime. -/
  isPrime : q.IsPrime
  /-- The quotient by a rig-closed ideal has Krull dimension one. -/
  ringKrullDim_quotient_eq_one : ringKrullDim (R ⧸ q) = 1
  /-- No ideal of definition is contained in a rig-closed prime. -/
  not_le_of_isIdealOfDefinition :
    ∀ I : Ideal R, TopologicalRing.Ideal.IsIdealOfDefinition I → ¬ I ≤ q

namespace IsRigClosed

/-- A rig-closed ideal is prime. -/
instance instIsPrime {R : Type u} [CommRing R] [TopologicalSpace R]
    [TopologicalRing.IsAdicRing R] [IsNoetherianRing R] (q : Ideal R)
    [h : IsRigClosed q] : q.IsPrime :=
  h.isPrime

/-- The quotient by a rig-closed ideal is a local ring. -/
instance instIsLocalRing_quotient {R : Type u} [CommRing R] [TopologicalSpace R]
    [TopologicalRing.IsAdicRing R] [IsNoetherianRing R] (q : Ideal R)
    [IsRigClosed q] : IsLocalRing (R ⧸ q) :=
  sorry

/-- Rig-closedness is equivalent to primeness, Krull dimension one of the
quotient, and avoidance of all ideals of definition. -/
theorem spec {R : Type u} [CommRing R] [TopologicalSpace R]
    [TopologicalRing.IsAdicRing R] [IsNoetherianRing R] (q : Ideal R) :
    IsRigClosed q ↔
      q.IsPrime ∧ ringKrullDim (R ⧸ q) = 1 ∧
        ∀ I : Ideal R, TopologicalRing.Ideal.IsIdealOfDefinition I → ¬ I ≤ q :=
  ⟨fun h ↦ ⟨h.isPrime, h.ringKrullDim_quotient_eq_one,
      h.not_le_of_isIdealOfDefinition⟩,
    fun h ↦ ⟨h.1, h.2.1, h.2.2⟩⟩

/-- The topological nilradical of the source lies in the inverse image of the
maximal ideal of the rig-closed quotient under the composite map. -/
theorem topologicalNilradical_le_comap_maximalIdeal {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalRing.IsAdicRing A] [TopologicalRing.IsAdicRing B]
    [IsNoetherianRing B] (φ : A →+* B) (hφ : Continuous φ)
    (q : Ideal B) [IsRigClosed q] :
    topologicalNilradical A ≤
      (maximalIdeal (B ⧸ q)).comap ((Quotient.mk q).comp φ) :=
  by
    obtain ⟨I, hI, hcomplete⟩ :=
      TopologicalRing.IsAdicRing.exists_ideal_isAdicComplete (R := B)
    letI := hcomplete
    let m := (maximalIdeal (B ⧸ q)).comap (Quotient.mk q)
    have hm : m.IsMaximal :=
      Ideal.comap_isMaximal_of_surjective _ Quotient.mk_surjective
    have hIm : I ≤ m :=
      le_trans (IsAdicComplete.le_jacobson_bot (I := I)) (sInf_le ⟨bot_le, hm⟩)
    intro x hx
    have hx' : IsTopologicallyNilpotent (φ x) :=
      (show IsTopologicallyNilpotent x from hx).map hφ
    have hopen : IsOpen (I : Set B) := by
      simpa using (isAdic_iff.mp hI).1 1
    obtain ⟨n, hn⟩ := hx'.exists_pow_mem_of_mem_nhds (hopen.mem_nhds I.zero_mem)
    exact hm.isPrime.mem_of_pow_mem n (hIm hn)

/-- The homomorphism from the source reduction to the residue field of a
rig-closed quotient induced by a continuous homomorphism. -/
def residueFieldHom {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalRing.IsAdicRing A] [TopologicalRing.IsAdicRing B]
    [IsNoetherianRing B] (φ : A →+* B) (hφ : Continuous φ)
    (q : Ideal B) [IsRigClosed q] :
    A ⧸ topologicalNilradical A →+* IsLocalRing.ResidueField (B ⧸ q) :=
  Ideal.quotientMap (maximalIdeal (B ⧸ q)) ((Quotient.mk q).comp φ)
    (topologicalNilradical_le_comap_maximalIdeal φ hφ q)

/-- The residue-field map sends the class of `x` to the residue of the
class of its image in the rig-closed quotient. -/
theorem residueFieldHom_apply {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalRing.IsAdicRing A] [TopologicalRing.IsAdicRing B]
    [IsNoetherianRing B] (φ : A →+* B) (hφ : Continuous φ)
    (q : Ideal B) [IsRigClosed q] (x : A) :
    residueFieldHom φ hφ q (Quotient.mk (topologicalNilradical A) x) =
      residue (B ⧸ q) (Quotient.mk q (φ x)) :=
  rfl

/-- For a continuous map of Noetherian adic rings, finite type of the
induced map on reductions implies finite type of the induced map to the
residue field of a rig-closed quotient. -/
theorem residueFieldHom_finiteType {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalRing.IsAdicRing A] [TopologicalRing.IsAdicRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    (φ : A →+* B) (hφ : Continuous φ)
    (h_finiteType : (φ.topologicalNilradicalQuotient hφ).FiniteType)
    (q : Ideal B) [q.IsRigClosed] :
    (residueFieldHom φ hφ q).FiniteType :=
  by
    let ψ := residueFieldHom (RingHom.id B) continuous_id q
    have hψ : Function.Surjective ψ :=
      Ideal.quotientMap_surjective Quotient.mk_surjective
    have hcomp : ψ.comp (φ.topologicalNilradicalQuotient hφ) =
        residueFieldHom φ hφ q := by
      apply Ideal.Quotient.ringHom_ext
      exact RingHom.ext fun _ ↦ rfl
    rw [← hcomp]
    exact h_finiteType.comp_surjective hψ

variable {A : Type u} [CommRing A] [TopologicalSpace A]
  [TopologicalRing.IsAdicRing A] [IsNoetherianRing A]

/-- Some topological ideal of definition is not contained in `q`, and `q` is
maximal among primes with this property. -/
def existsMaximal (q : Ideal A) : Prop :=
  ∃ I : Ideal A, TopologicalRing.Ideal.IsIdealOfDefinition I ∧
    Maximal (fun r : Ideal A ↦ r.IsPrime ∧ ¬ I ≤ r) q

/-- For some topological ideal of definition `I`, the prime `p` is a closed
point of `PrimeSpectrum A` minus `zeroLocus I`. -/
def existsClosedPoint (p : PrimeSpectrum A) : Prop :=
  ∃ I : Ideal A, TopologicalRing.Ideal.IsIdealOfDefinition I ∧
    p ∉ PrimeSpectrum.zeroLocus I ∧
      closure {p} ∩ (PrimeSpectrum.zeroLocus I)ᶜ = {p}

/-- Every topological ideal of definition is not contained in `q`, and `q` is
maximal among primes with this property. -/
def forallMaximal (q : Ideal A) : Prop :=
  ∀ I : Ideal A, TopologicalRing.Ideal.IsIdealOfDefinition I →
    Maximal (fun r : Ideal A ↦ r.IsPrime ∧ ¬ I ≤ r) q

/-- For every topological ideal of definition `I`, the prime `p` is a closed
point of `PrimeSpectrum A` minus `zeroLocus I`. -/
def forallClosedPoint (p : PrimeSpectrum A) : Prop :=
  ∀ I : Ideal A, TopologicalRing.Ideal.IsIdealOfDefinition I →
    p ∉ PrimeSpectrum.zeroLocus I ∧
      closure {p} ∩ (PrimeSpectrum.zeroLocus I)ᶜ = {p}

/-- The quotient has Krull dimension one and some topological ideal of definition
is not contained in `q`. -/
def dimOneExistsNotLe (q : Ideal A) : Prop :=
  ringKrullDim (A ⧸ q) = 1 ∧
    ∃ I : Ideal A, TopologicalRing.Ideal.IsIdealOfDefinition I ∧ ¬ I ≤ q

/-- The quotient has Krull dimension one and no topological ideal of definition
is contained in `q`. -/
def dimOneForallNotLe (q : Ideal A) : Prop :=
  ringKrullDim (A ⧸ q) = 1 ∧
    ∀ I : Ideal A, TopologicalRing.Ideal.IsIdealOfDefinition I → ¬ I ≤ q

/-- The quotient has Krull dimension one and its induced quotient topology is
not discrete. -/
def dimOneNontrivialTopology (q : Ideal A) : Prop :=
  ringKrullDim (A ⧸ q) = 1 ∧ ¬ DiscreteTopology (A ⧸ q)

/-- The quotient is a one-dimensional Noetherian complete local domain whose
maximal ideal is the radical of the image of every topological ideal of definition. -/
def isCompleteLocalDomain (q : Ideal A) : Prop :=
  IsCompleteLocalRing (A ⧸ q) ∧ IsDomain (A ⧸ q) ∧ IsNoetherianRing (A ⧸ q) ∧
    ringKrullDim (A ⧸ q) = 1 ∧
      ∀ I : Ideal A, TopologicalRing.Ideal.IsIdealOfDefinition I →
        (I.map (Ideal.Quotient.mk q)).radical.IsMaximal

omit [IsNoetherianRing A] in
private theorem exists_ideal_of_definition :
    ∃ I : Ideal A, TopologicalRing.Ideal.IsIdealOfDefinition I := by
  obtain ⟨I, hI, _⟩ :=
    TopologicalRing.IsAdicRing.exists_ideal_isAdicComplete (R := A)
  refine ⟨I, ?_, (isAdic_iff.mp hI).2⟩
  simpa using (isAdic_iff.mp hI).1 1

omit [TopologicalRing.IsAdicRing A] [IsNoetherianRing A] in
private theorem not_le_iff_of_isIdealOfDefinition (q : Ideal A) [q.IsPrime]
    (I J : Ideal A) (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
    (hJ : TopologicalRing.Ideal.IsIdealOfDefinition J) :
    (¬ I ≤ q) ↔ ¬ J ≤ q := by
  apply not_congr
  constructor
  · intro hIq
    obtain ⟨n, hn⟩ := hJ.2 I (hI.1.mem_nhds I.zero_mem)
    exact Ideal.IsPrime.le_of_pow_le ((show J ^ n ≤ I from hn).trans hIq)
  · intro hJq
    obtain ⟨n, hn⟩ := hI.2 J (hJ.1.mem_nhds J.zero_mem)
    exact Ideal.IsPrime.le_of_pow_le ((show I ^ n ≤ J from hn).trans hJq)

omit [TopologicalSpace A] [TopologicalRing.IsAdicRing A] [IsNoetherianRing A] in
private theorem maximal_iff_closedPoint (p : PrimeSpectrum A) (I : Ideal A) :
    Maximal (fun r : Ideal A ↦ r.IsPrime ∧ ¬ I ≤ r) p.asIdeal ↔
      p ∉ PrimeSpectrum.zeroLocus I ∧
        closure {p} ∩ (PrimeSpectrum.zeroLocus I)ᶜ = {p} := by
  constructor
  · intro h
    refine ⟨h.prop.2, ?_⟩
    rw [PrimeSpectrum.closure_singleton]
    ext r
    constructor
    · rintro ⟨hr, hIr⟩
      change p.asIdeal ≤ r.asIdeal at hr
      change ¬ I ≤ r.asIdeal at hIr
      apply Set.mem_singleton_iff.mpr
      apply PrimeSpectrum.ext
      exact le_antisymm (h.2 ⟨r.isPrime, hIr⟩ hr) hr
    · rintro rfl
      exact ⟨(PrimeSpectrum.mem_zeroLocus _ _).mpr Set.Subset.rfl, h.prop.2⟩
  · rintro ⟨hIp, hclosed⟩
    refine ⟨⟨p.isPrime, hIp⟩, ?_⟩
    intro r hr hpr
    let r' : PrimeSpectrum A := ⟨r, hr.1⟩
    have hmem : r' ∈ closure {p} ∩ (PrimeSpectrum.zeroLocus I)ᶜ := by
      rw [PrimeSpectrum.closure_singleton]
      exact ⟨hpr, hr.2⟩
    rw [hclosed] at hmem
    exact le_of_eq (congrArg PrimeSpectrum.asIdeal (Set.mem_singleton_iff.mp hmem))

/-- Rig-closedness is equivalent to maximality among primes avoiding some
topological ideal of definition. -/
theorem iff_existsMaximal (q : Ideal A) :
    IsRigClosed q ↔ existsMaximal q :=
  sorry

/-- Rig-closedness is equivalent to being a closed point of
`PrimeSpectrum A` minus `zeroLocus I` for some topological ideal of
definition `I`. -/
theorem iff_existsClosedPoint (p : PrimeSpectrum A) :
    IsRigClosed p.asIdeal ↔ existsClosedPoint p :=
  by
    rw [iff_existsMaximal]
    unfold existsMaximal existsClosedPoint
    exact exists_congr fun I ↦ and_congr_right fun _ ↦ maximal_iff_closedPoint p I

/-- Rig-closedness is equivalent to maximality among primes avoiding every
topological ideal of definition. -/
theorem iff_forallMaximal (q : Ideal A) :
    IsRigClosed q ↔ forallMaximal q :=
  by
    rw [iff_existsMaximal]
    constructor
    · rintro ⟨I, hI, hmax⟩ J hJ
      haveI := hmax.prop.1
      refine ⟨⟨hmax.prop.1,
        (not_le_iff_of_isIdealOfDefinition q I J hI hJ).mp hmax.prop.2⟩, ?_⟩
      intro r hr hqr
      haveI := hr.1
      exact hmax.2
        ⟨hr.1, (not_le_iff_of_isIdealOfDefinition r I J hI hJ).mpr hr.2⟩ hqr
    · intro h
      obtain ⟨I, hI⟩ := exists_ideal_of_definition (A := A)
      exact ⟨I, hI, h I hI⟩

/-- Rig-closedness is equivalent to being a closed point of
`PrimeSpectrum A` minus `zeroLocus I` for every topological ideal of
definition `I`. -/
theorem iff_forallClosedPoint (p : PrimeSpectrum A) :
    IsRigClosed p.asIdeal ↔ forallClosedPoint p :=
  by
    rw [iff_forallMaximal]
    simp only [forallMaximal, forallClosedPoint, maximal_iff_closedPoint]

/-- Rig-closedness is equivalent to primeness together with dimension one and
existence of a topological ideal of definition not contained in the prime. -/
theorem iff_dimOneExistsNotLe (q : Ideal A) :
    IsRigClosed q ↔ q.IsPrime ∧ dimOneExistsNotLe q :=
  by
    rw [spec]
    constructor
    · rintro ⟨hq, hdim, hnot⟩
      obtain ⟨I, hI⟩ := exists_ideal_of_definition (A := A)
      exact ⟨hq, hdim, I, hI, hnot I hI⟩
    · rintro ⟨hq, hdim, I, hI, hnot⟩
      haveI := hq
      exact ⟨hq, hdim, fun J hJ ↦
        (not_le_iff_of_isIdealOfDefinition q I J hI hJ).mp hnot⟩

/-- Rig-closedness is equivalent to primeness together with dimension one and
avoidance of every topological ideal of definition. -/
theorem iff_dimOneForallNotLe (q : Ideal A) :
    IsRigClosed q ↔ q.IsPrime ∧ dimOneForallNotLe q :=
  spec q

/-- Rig-closedness is equivalent to primeness together with dimension one and
nondiscreteness of the induced topology on the quotient. -/
theorem iff_nontrivialTopology (q : Ideal A) :
    IsRigClosed q ↔ q.IsPrime ∧ dimOneNontrivialTopology q :=
  by
    rw [spec]
    have hquot : DiscreteTopology (A ⧸ q) ↔ IsOpen (q : Set A) :=
      QuotientAddGroup.discreteTopology_iff
    constructor
    · rintro ⟨hq, hdim, hnot⟩
      haveI := hq
      refine ⟨hq, hdim, ?_⟩
      intro hdiscrete
      obtain ⟨I, hI⟩ := exists_ideal_of_definition (A := A)
      obtain ⟨n, hn⟩ := hI.2 q ((hquot.mp hdiscrete).mem_nhds q.zero_mem)
      exact hnot I hI (Ideal.IsPrime.le_of_pow_le (show I ^ n ≤ q from hn))
    · rintro ⟨hq, hdim, hnot⟩
      refine ⟨hq, hdim, ?_⟩
      intro I hI hIq
      apply hnot
      apply discreteTopology_iff_isOpen_singleton_zero.mpr
      have himage : Ideal.Quotient.mk q '' (I : Set A) = {0} := by
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩
          exact Set.mem_singleton_iff.mpr (Ideal.Quotient.eq_zero_iff_mem.mpr (hIq hy))
        · rintro rfl
          exact ⟨0, I.zero_mem, map_zero _⟩
      rw [← himage]
      exact QuotientRing.isOpenMap_coe q I hI.1

/-- Rig-closedness is equivalent to the quotient being a one-dimensional
Noetherian complete local domain whose maximal ideal is the radical of the
image of every topological ideal of definition. -/
theorem iff_isCompleteLocalDomain (q : Ideal A) :
    IsRigClosed q ↔ isCompleteLocalDomain q :=
  sorry

/-- The complete-local-domain condition is equivalent to requiring each
radical image of an ideal of definition to equal the unique maximal ideal. -/
theorem isCompleteLocalDomain_iff (q : Ideal A) :
    isCompleteLocalDomain q ↔
      IsCompleteLocalRing (A ⧸ q) ∧ IsDomain (A ⧸ q) ∧
        IsNoetherianRing (A ⧸ q) ∧ ringKrullDim (A ⧸ q) = 1 ∧
        ∀ [IsCompleteLocalRing (A ⧸ q)] (I : Ideal A),
          TopologicalRing.Ideal.IsIdealOfDefinition I →
            (I.map (Ideal.Quotient.mk q)).radical = maximalIdeal (A ⧸ q) :=
  by
    constructor
    · rintro ⟨hlocal, hdomain, hnoeth, hdim, hmax⟩
      refine ⟨hlocal, hdomain, hnoeth, hdim, ?_⟩
      intro hcomplete I hI
      letI := hcomplete
      exact eq_maximalIdeal (hmax I hI)
    · rintro ⟨hlocal, hdomain, hnoeth, hdim, heq⟩
      letI := hlocal
      refine ⟨hlocal, hdomain, hnoeth, hdim, ?_⟩
      intro I hI
      rw [heq I hI]
      infer_instance

/-- The quotient by a rig-closed prime is a complete local ring. -/
instance isCompleteLocalRing_quotient (q : Ideal A) [IsRigClosed q] :
    IsCompleteLocalRing (A ⧸ q) :=
  ((iff_isCompleteLocalDomain q).mp inferInstance).1

end IsRigClosed

end Ideal

namespace PrimeSpectrum

variable {A : Type u} [CommRing A] [TopologicalSpace A]
  [TopologicalRing.IsAdicRing A] [IsNoetherianRing A]

/-- A point of the prime spectrum is rig-closed when its underlying ideal is rig-closed. -/
abbrev IsRigClosed (q : PrimeSpectrum A) : Prop :=
  q.asIdeal.IsRigClosed

open Ideal.IsRigClosed

/-- For a prime of a Noetherian adic ring, maximal avoidance, relative
closedness, dimension one with ideal avoidance, nondiscrete quotient topology,
and the complete-local-domain condition give eight equivalent characterizations. -/
theorem isRigClosed_tfae (q : PrimeSpectrum A) :
    List.TFAE
      [ existsMaximal q.asIdeal, existsClosedPoint q
      , forallMaximal q.asIdeal, forallClosedPoint q
      , dimOneExistsNotLe q.asIdeal, dimOneForallNotLe q.asIdeal
      , dimOneNontrivialTopology q.asIdeal
      , isCompleteLocalDomain q.asIdeal ] :=
  by
    apply List.tfae_of_forall (Ideal.IsRigClosed q.asIdeal)
    intro P hP
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
    rcases hP with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (iff_existsMaximal q.asIdeal).symm
    · exact (iff_existsClosedPoint q).symm
    · exact (iff_forallMaximal q.asIdeal).symm
    · exact (iff_forallClosedPoint q).symm
    · simpa only [q.isPrime, true_and] using (iff_dimOneExistsNotLe q.asIdeal).symm
    · simpa only [q.isPrime, true_and] using (iff_dimOneForallNotLe q.asIdeal).symm
    · simpa only [q.isPrime, true_and] using (iff_nontrivialTopology q.asIdeal).symm
    · exact (iff_isCompleteLocalDomain q.asIdeal).symm

end PrimeSpectrum
