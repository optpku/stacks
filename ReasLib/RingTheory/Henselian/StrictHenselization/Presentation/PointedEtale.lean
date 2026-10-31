/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Tactic.CrossRefAttribute
import Mathlib.RingTheory.Unramified.LocalStructure
public import ReasLib.Algebra.Category.CommAlgCat.Over.Etale.Localization
public import ReasLib.Algebra.Category.CommAlgCat.Over.Target.Localization
public import ReasLib.Algebra.Category.CommAlgCat.Over.Target.Localization.SeparableClosure
public import ReasLib.RingTheory.Henselian.StrictHenselization
public import ReasLib.RingTheory.Henselian.StrictHenselization.ResidueField
public import ReasLib.RingTheory.Henselian.StrictHenselization.ResidueCoordinate
public import ReasLib.RingTheory.LocalRing.ResidueField.MaximalIdeal

@[expose] public section

/-!
# Pointed-etale presentations of strict henselizations

This leaf is the reusable presentation layer for a strict henselization.  The
pointed-etale category and its prime-localization diagram are owned by
CommAlgCat.Over.Etale.Localization; this file only records the residue-field
coordinates, the lifting predicate, and the resulting presentation interface.

The coordinate on the source is canonical: it is induced by the map
R → K whose kernel is p.  The coordinate on the target strict henselization
is supplied explicitly, since an identification of its residue field with an
external field is not canonical.

@stack 04GW
-/

open CategoryTheory
open CategoryTheory.Limits
open IsLocalRing
open Polynomial

universe u v

noncomputable section

namespace IsStrictHenselizationOf.PointedEtale

private theorem simpleRoot_eq_of_residue_eq
    {T : Type*} [CommRing T] [IsLocalRing T]
    (P : T[X]) {a b : T} (ha : P.eval a = 0) (hb : P.eval b = 0)
    (hd : IsUnit (P.derivative.eval a)) (hr : residue T a = residue T b) : a = b := by
  obtain ⟨Q, hQ⟩ := Polynomial.dvd_iff_isRoot.mpr ha
  have hda : P.derivative.eval a = Q.eval a := by
    rw [hQ]
    simp
  rw [hda] at hd
  have hrQ : residue T (Q.eval b) = residue T (Q.eval a) := by
    rw [← Polynomial.eval₂_at_apply, ← Polynomial.eval₂_at_apply, hr]
  have hu : IsUnit (Q.eval b) := (residue_ne_zero_iff_isUnit _).mp
    (hrQ ▸ (residue_ne_zero_iff_isUnit _).mpr hd)
  have hz : (b - a) * Q.eval b = 0 := by
    simpa [hQ] using hb
  exact (sub_eq_zero.mp (hu.mul_left_eq_zero.mp hz)).symm

-- Use Mathlib instances to keep this proof independent of the deferred essentially-etale bridge.
attribute [-instance] Algebra.EssEtale.of_etale in
private theorem etaleHom_ext
    {R A T : Type*} [CommRing R] [CommRing A] [CommRing T]
    [Algebra R A] [Algebra R T] [IsLocalRing T] [Algebra.Etale R A]
    (f g : A →ₐ[R] T) (h : ∀ a, residue T (f a) = residue T (g a)) : f = g := by
  have hstd (P : StandardEtalePair R) (f g : P.Ring →ₐ[R] T)
      (h : ∀ a, residue T (f a) = residue T (g a)) : f = g := by
    apply P.hom_ext
    let Q := P.map (algebraMap R T)
    have hf : Q.HasMap (f P.X) := (P.hasMap_X.map f).map_algebraMap
    have hg : Q.HasMap (g P.X) := (P.hasMap_X.map g).map_algebraMap
    exact simpleRoot_eq_of_residue_eq Q.f
      (by simpa [Polynomial.aeval_def] using hf.1)
      (by simpa [Polynomial.aeval_def] using hg.1)
      (by simpa [Polynomial.aeval_def] using hf.isUnit_derivative_f) (h P.X)
  let q := RingHom.ker ((residue T).comp f.toRingHom)
  haveI : q.IsPrime := RingHom.ker_isPrime _
  obtain ⟨s, hs, hstds⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := R) q
  letI : Algebra.IsStandardEtale R (Localization.Away s) := hstds
  have hf : IsUnit (f s) := (residue_ne_zero_iff_isUnit _).mp hs
  have hg : IsUnit (g s) := (residue_ne_zero_iff_isUnit _).mp (h s ▸ hs)
  let fs : Localization.Away s →ₐ[R] T := IsLocalization.Away.liftAlgHom s hf (f := f)
  let gs : Localization.Away s →ₐ[R] T := IsLocalization.Away.liftAlgHom s hg (f := g)
  have hres : (residue T).comp fs.toRingHom = (residue T).comp gs.toRingHom := by
    apply IsLocalization.ringHom_ext (Submonoid.powers s)
    ext a
    simpa [fs, gs, IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq] using h a
  obtain ⟨P⟩ := Algebra.IsStandardEtale.nonempty_standardEtalePresentation
    (R := R) (S := Localization.Away s)
  have he : fs.comp P.equivRing.symm.toAlgHom = gs.comp P.equivRing.symm.toAlgHom :=
    hstd P.P _ _ (fun a => DFunLike.congr_fun hres (P.equivRing.symm a))
  have he' : fs = gs := by
    apply AlgHom.ext
    intro a
    simpa using AlgHom.congr_fun he (P.equivRing a)
  ext a
  have hh := AlgHom.congr_fun he' (algebraMap A (Localization.Away s) a)
  simpa [fs, gs, IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq] using hh

private theorem exists_standard_residue_lift
    {R T : Type*} [CommRing R] [CommRing T] [Algebra R T] [HenselianLocalRing T]
    (P : StandardEtalePair R) (τ : P.Ring →ₐ[R] ResidueField T) :
    ∃ f : P.Ring →ₐ[R] T, ∀ a, residue T (f a) = τ a := by
  let Q := P.map (algebraMap R T)
  have hκ : Q.HasMap (τ P.X) := (P.hasMap_X.map τ).map_algebraMap
  have hd : aeval (τ P.X) Q.f.derivative ≠ 0 :=
    isUnit_iff_ne_zero.mp hκ.isUnit_derivative_f
  obtain ⟨a, ha, hres⟩ := ((HenselianLocalRing.TFAE T).out 0 1 rfl rfl).mp
    (inferInstance : HenselianLocalRing T) Q.f Q.monic_f (τ P.X) hκ.1 hd
  have hmap : P.HasMap a := by
    refine ⟨?_, ?_⟩
    · simpa [Q, StandardEtalePair.map, Polynomial.IsRoot, Polynomial.aeval_def] using ha
    · apply (residue_ne_zero_iff_isUnit _).mp
      have hg : aeval (τ P.X) Q.g ≠ 0 := isUnit_iff_ne_zero.mp hκ.2
      have hEval := Polynomial.aeval_algHom_apply
        (Ideal.Quotient.mkₐ T (maximalIdeal T)) a Q.g
      have hg' : residue T (aeval (R := T) a Q.g) ≠ 0 := by
        change (Ideal.Quotient.mkₐ T (maximalIdeal T)) (aeval a Q.g) ≠ 0
        rw [← hEval]
        change aeval (residue T a) Q.g ≠ 0
        rw [hres]
        exact hg
      simpa [Q, StandardEtalePair.map, Polynomial.aeval_def] using hg'
  refine ⟨P.lift a hmap, ?_⟩
  have he : (IsScalarTower.toAlgHom R T (ResidueField T)).comp (P.lift a hmap) = τ := by
    apply P.hom_ext
    simpa using hres
  exact fun b => AlgHom.congr_fun he b

-- Use Mathlib instances to keep this proof independent of the deferred essentially-etale bridge.
attribute [-instance] Algebra.EssEtale.of_etale in
private theorem exists_etale_residue_lift
    {R A T : Type*} [CommRing R] [CommRing A] [CommRing T]
    [Algebra R A] [Algebra R T] [HenselianLocalRing T] [Algebra.Etale R A]
    (τ : A →ₐ[R] ResidueField T) :
    ∃ f : A →ₐ[R] T, ∀ a, residue T (f a) = τ a := by
  let q := RingHom.ker τ.toRingHom
  haveI : q.IsPrime := RingHom.ker_isPrime _
  obtain ⟨s, hs, hstds⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := R) q
  letI : Algebra.IsStandardEtale R (Localization.Away s) := hstds
  let τs : Localization.Away s →ₐ[R] ResidueField T :=
    IsLocalization.Away.liftAlgHom s (isUnit_iff_ne_zero.mpr hs) (f := τ)
  obtain ⟨P⟩ := Algebra.IsStandardEtale.nonempty_standardEtalePresentation
    (R := R) (S := Localization.Away s)
  obtain ⟨f, hf⟩ := exists_standard_residue_lift P.P (τs.comp P.equivRing.symm.toAlgHom)
  refine ⟨(f.comp P.equivRing.toAlgHom).comp
    (IsScalarTower.toAlgHom R A (Localization.Away s)), ?_⟩
  intro a
  simp only [AlgHom.comp_apply, IsScalarTower.toAlgHom_apply, hf,
    AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply]
  simp [τs, IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]


section

variable {R : Type u} [CommRing R]
variable {K : Type v} [Field K] [Algebra R K]
variable {p : Ideal R} [p.IsPrime]
variable (hbase : RingHom.ker (algebraMap R K) = p)

/-! ### Target coordinate and lifting predicate -/

/-- The residue-field coordinate specialized to the canonical base
localization at `p`.  The neutral coordinate owner lives in
`IsStrictHenselizationOf.ResidueField`; this abbreviation only supplies the
prime-localized base map used by the pointed-etale presentation. -/
@[stacks 04GW "pointed-etale strict-henselization residue coordinate"]
noncomputable abbrev Coordinate
    (hbase : RingHom.ker (algebraMap R K) = p)
    (Rsh : Type v) [CommRing Rsh]
    [Algebra (Localization.AtPrime p) Rsh]
    [IsStrictHenselizationOf (Localization.AtPrime p) Rsh] :=
  IsStrictHenselizationOf.ResidueField.Coordinate
    (L := Localization.AtPrime p) (S := Rsh) (K := K)
    (CommAlgCat.Over.Target.Localization.baseResidueMap hbase)

namespace Coordinate

variable {Rsh : Type v} [CommRing Rsh]
variable [Algebra (Localization.AtPrime p) Rsh]
variable [IsStrictHenselizationOf (Localization.AtPrime p) Rsh]

/- The generic owner supplies the maximal-ideal coordinate.  This thin
specialization keeps the source-facing namespace stable while avoiding a
second structure definition. -/

/-- The same target coordinate expressed on the maximal-ideal residue field. -/
@[stacks 04GW "maximal-ideal strict-henselization residue coordinate"]
noncomputable abbrev maximalIdealEquiv
    (coordinate : Coordinate (R := R) (K := K) hbase Rsh) :
    (maximalIdeal Rsh).ResidueField ≃+* K :=
  IsStrictHenselizationOf.ResidueField.Coordinate.maximalIdealEquiv coordinate

/-- The maximal-ideal form of target-coordinate compatibility. -/
@[stacks 04GW "maximal-ideal residue-coordinate compatibility"]
theorem maximalIdealEquiv_comp
    (coordinate : Coordinate (R := R) (K := K) hbase Rsh) :
    (coordinate.maximalIdealEquiv).toRingHom.comp
        (Ideal.ResidueField.map
          (maximalIdeal (Localization.AtPrime p)) (maximalIdeal Rsh)
          (algebraMap (Localization.AtPrime p) Rsh)
          (IsLocalRing.maximalIdeal_comap
            (algebraMap (Localization.AtPrime p) Rsh)).symm) =
      CommAlgCat.Over.Target.Localization.baseResidueFieldMap hbase := by
  change (coordinate.equiv.toRingHom.comp
      (IsLocalRing.ResidueField.maximalIdealAlgEquiv Rsh).symm.toRingHom).comp _ = _
  rw [RingHom.comp_assoc,
    IsLocalRing.ResidueField.maximalIdealAlgEquiv_symm_naturality,
    ← RingHom.comp_assoc, coordinate.commutes]
  ext x
  simp [CommAlgCat.Over.Target.Localization.baseResidueMap]

private theorem equiv_apply_residue_base (coordinate : Coordinate (R := R) (K := K) hbase Rsh)
    (r : R) :
    coordinate.equiv
      (residue Rsh (algebraMap (Localization.AtPrime p) Rsh
        (algebraMap R (Localization.AtPrime p) r))) = algebraMap R K r := by
  have h := DFunLike.congr_fun coordinate.commutes
    (residue (Localization.AtPrime p) (algebraMap R (Localization.AtPrime p) r))
  simp only [RingHom.comp_apply, IsLocalRing.ResidueField.map_residue] at h
  refine h.trans ?_
  change (CommAlgCat.Over.Target.ResidueField.baseMap hbase)
    ((ResidueField.maximalIdealAlgEquiv (Localization.AtPrime p)).symm
      ((ResidueField.maximalIdealAlgEquiv (Localization.AtPrime p))
        (residue (Localization.AtPrime p) (algebraMap R (Localization.AtPrime p) r)))) = _
  rw [AlgEquiv.symm_apply_apply]
  change (Ideal.ResidueField.lift p (algebraMap R K) _ _)
    (algebraMap R p.ResidueField r) = _
  simp only [Ideal.ResidueField.lift_algebraMap]


end Coordinate

/-- Source-facing name for the shared underlying localized pointed-etale map.
The relative source algebra is pinned only in the neutral localization owner. -/
@[stacks 04GW "underlying map of a localized pointed-etale morphism"]
noncomputable abbrev ringHom
    {S : Type v} [CommRing S] [Algebra (Localization.AtPrime p) S]
    (A : CommAlgCat.Over.Etale.category R K)
    (f : CommAlgCat.Over.Target.Localization.object hbase A.obj ⟶
      CommAlgCat.of (Localization.AtPrime p) S) :
    Localization.AtPrime (CommAlgCat.Over.Target.kernel A.obj) →+* S :=
  CommAlgCat.Over.Target.Localization.ringHom hbase A.obj f

private theorem ringHom_apply_base
    {S : Type v} [CommRing S] [Algebra (Localization.AtPrime p) S]
    (A : CommAlgCat.Over.Etale.category R K)
    (f : CommAlgCat.Over.Target.Localization.object hbase A.obj ⟶
      CommAlgCat.of (Localization.AtPrime p) S) (r : R) :
    ringHom hbase A f
      (algebraMap A.obj.left
        (Localization.AtPrime (CommAlgCat.Over.Target.kernel A.obj))
        (algebraMap R A.obj.left r)) =
      algebraMap (Localization.AtPrime p) S (algebraMap R (Localization.AtPrime p) r) := by
  letI := CommAlgCat.Over.Target.Localization.algebra hbase A.obj
  change f.hom
    (algebraMap A.obj.left
      (Localization.AtPrime (CommAlgCat.Over.Target.kernel A.obj))
      (algebraMap R A.obj.left r)) = _
  calc
    _ = f.hom
        (algebraMap (Localization.AtPrime p)
          (Localization.AtPrime (CommAlgCat.Over.Target.kernel A.obj))
          (algebraMap R (Localization.AtPrime p) r)) := by
      exact congrArg f.hom
        (Localization.localRingHom_to_map p
          (CommAlgCat.Over.Target.kernel A.obj) (algebraMap R A.obj.left)
          (CommAlgCat.Over.Target.baseComap hbase A.obj) r).symm
    _ = _ := f.hom.commutes _


/-- A localized algebra morphism is a residue-compatible lift when it induces
the selected pointed-etale residue map. -/
@[stacks 04GW "residue-compatible pointed-etale lift"]
def IsLift
    {Rsh : Type v} [CommRing Rsh]
    [Algebra (Localization.AtPrime p) Rsh]
    [IsStrictHenselizationOf (Localization.AtPrime p) Rsh]
    (coordinate : Coordinate (R := R) (K := K) hbase Rsh)
    (A : CommAlgCat.Over.Etale.category R K)
    (f : CommAlgCat.Over.Target.Localization.object hbase A.obj ⟶
      CommAlgCat.of (Localization.AtPrime p) Rsh) : Prop :=
  ∃ hq :
      maximalIdeal (Localization.AtPrime (CommAlgCat.Over.Target.kernel A.obj)) =
        Ideal.comap (ringHom hbase A f) (maximalIdeal Rsh),
    (coordinate.maximalIdealEquiv).toRingHom.comp
        (Ideal.ResidueField.map
          (maximalIdeal (Localization.AtPrime (CommAlgCat.Over.Target.kernel A.obj)))
          (maximalIdeal Rsh) (ringHom hbase A f) hq) =
      CommAlgCat.Over.Target.Localization.residueFieldMap A.obj

private theorem isLift_iff_residue
    {Rsh : Type v} [CommRing Rsh]
    [Algebra (Localization.AtPrime p) Rsh]
    [IsStrictHenselizationOf (Localization.AtPrime p) Rsh]
    (coordinate : Coordinate (R := R) (K := K) hbase Rsh)
    (A : CommAlgCat.Over.Etale.category R K)
    (f : CommAlgCat.Over.Target.Localization.object hbase A.obj ⟶
      CommAlgCat.of (Localization.AtPrime p) Rsh) :
    IsLift (hbase := hbase) coordinate A f ↔
      (coordinate.equiv.toRingHom.comp (residue Rsh)).comp (ringHom hbase A f) =
        (CommAlgCat.Over.Target.ResidueField.map A.obj).comp
          (residue (Localization.AtPrime (CommAlgCat.Over.Target.kernel A.obj))) := by
  constructor
  · rintro ⟨hq, hr⟩
    apply RingHom.ext
    intro z
    have h := DFunLike.congr_fun hr
      (algebraMap (Localization.AtPrime (CommAlgCat.Over.Target.kernel A.obj))
        (maximalIdeal
          (Localization.AtPrime (CommAlgCat.Over.Target.kernel A.obj))).ResidueField z)
    simp only [RingHom.comp_apply, Ideal.ResidueField.map_algebraMap] at h
    change coordinate.equiv
        ((ResidueField.maximalIdealAlgEquiv Rsh).symm
          (algebraMap Rsh (maximalIdeal Rsh).ResidueField (ringHom hbase A f z))) =
      (CommAlgCat.Over.Target.ResidueField.map A.obj)
        ((ResidueField.maximalIdealAlgEquiv
          (Localization.AtPrime (CommAlgCat.Over.Target.kernel A.obj))).symm
          (algebraMap (Localization.AtPrime (CommAlgCat.Over.Target.kernel A.obj))
            (maximalIdeal
              (Localization.AtPrime (CommAlgCat.Over.Target.kernel A.obj))).ResidueField z)) at h
    change coordinate.equiv (residue Rsh (ringHom hbase A f z)) =
      (CommAlgCat.Over.Target.ResidueField.map A.obj) (residue _ z)
    simpa only [ResidueField.maximalIdealAlgEquiv_symm_apply_algebraMap] using h
  · intro hr
    have hq : maximalIdeal
        (Localization.AtPrime (CommAlgCat.Over.Target.kernel A.obj)) =
          Ideal.comap (ringHom hbase A f) (maximalIdeal Rsh) := by
      ext z
      change z ∈ maximalIdeal _ ↔ ringHom hbase A f z ∈ maximalIdeal Rsh
      rw [← residue_eq_zero_iff, ← residue_eq_zero_iff]
      have h := DFunLike.congr_fun hr z
      change coordinate.equiv (residue Rsh (ringHom hbase A f z)) =
        (CommAlgCat.Over.Target.ResidueField.map A.obj) (residue _ z) at h
      constructor
      · intro hz
        apply coordinate.equiv.injective
        simpa [hz] using h
      · intro hz
        apply RingHom.injective (CommAlgCat.Over.Target.ResidueField.map A.obj)
        simpa [hz] using h.symm
    refine ⟨hq, ?_⟩
    apply Ideal.ResidueField.ringHom_ext
    apply RingHom.ext
    intro z
    simp only [RingHom.comp_apply, Ideal.ResidueField.map_algebraMap]
    change coordinate.equiv
        ((ResidueField.maximalIdealAlgEquiv Rsh).symm
          (algebraMap Rsh (maximalIdeal Rsh).ResidueField (ringHom hbase A f z))) =
      (CommAlgCat.Over.Target.ResidueField.map A.obj)
        ((ResidueField.maximalIdealAlgEquiv
          (Localization.AtPrime (CommAlgCat.Over.Target.kernel A.obj))).symm
          (algebraMap (Localization.AtPrime (CommAlgCat.Over.Target.kernel A.obj))
            (maximalIdeal
              (Localization.AtPrime (CommAlgCat.Over.Target.kernel A.obj))).ResidueField z))
    have h := DFunLike.congr_fun hr z
    change coordinate.equiv (residue Rsh (ringHom hbase A f z)) =
      (CommAlgCat.Over.Target.ResidueField.map A.obj) (residue _ z) at h
    simpa only [ResidueField.maximalIdealAlgEquiv_symm_apply_algebraMap] using h


/-! ### The lift API -/

/-- A chosen residue-compatible lift.  The map and both residue conditions are
explicit data, so consumers never inspect a witness chosen from an existence
theorem. -/
@[stacks 04GW "chosen pointed-etale strict-henselization lift"]
structure Lift
    {Rsh : Type v} [CommRing Rsh]
    [Algebra (Localization.AtPrime p) Rsh]
    [IsStrictHenselizationOf (Localization.AtPrime p) Rsh]
    (coordinate : Coordinate (R := R) (K := K) hbase Rsh)
    (A : CommAlgCat.Over.Etale.category R K) where
  /-- The localized algebra morphism selected by this lift. -/
  hom : CommAlgCat.Over.Target.Localization.object hbase A.obj ⟶
    CommAlgCat.of (Localization.AtPrime p) Rsh
  /-- The selected map pulls back the target maximal ideal to the selected
  maximal ideal of the localized pointed-etale object. -/
  comap_maximalIdeal :
    maximalIdeal (Localization.AtPrime (CommAlgCat.Over.Target.kernel A.obj)) =
      Ideal.comap (ringHom hbase A hom) (maximalIdeal Rsh)
  /-- The selected map induces the prescribed maximal-ideal residue coordinate. -/
  residueMap_eq :
    (coordinate.maximalIdealEquiv).toRingHom.comp
        (Ideal.ResidueField.map
          (maximalIdeal (Localization.AtPrime (CommAlgCat.Over.Target.kernel A.obj)))
          (maximalIdeal Rsh) (ringHom hbase A hom) comap_maximalIdeal) =
      CommAlgCat.Over.Target.Localization.residueFieldMap A.obj

namespace Lift

variable {Rsh : Type v} [CommRing Rsh]
variable [Algebra (Localization.AtPrime p) Rsh]
variable [IsStrictHenselizationOf (Localization.AtPrime p) Rsh]
variable (coordinate : Coordinate (R := R) (K := K) hbase Rsh)
variable (A : CommAlgCat.Over.Etale.category R K)

/- The two defining fields above are exposed individually; this proposition is
the compact source-facing form used by the universal-property theorem. -/
/-- The selected map satisfies the residue-coordinate lifting condition. -/
@[stacks 04GW "specification of a chosen pointed-etale lift"]
theorem spec (lift : Lift (hbase := hbase) coordinate A) :
    IsLift (hbase := hbase) coordinate A lift.hom := by
  exact ⟨lift.comap_maximalIdeal, lift.residueMap_eq⟩

/-- Any two residue-compatible lifts of the same pointed-etale object agree. -/
@[stacks 04GW "uniqueness of a chosen pointed-etale lift"]
theorem unique
    (lift : Lift (hbase := hbase) coordinate A) (g :
      CommAlgCat.Over.Target.Localization.object hbase A.obj ⟶
        CommAlgCat.of (Localization.AtPrime p) Rsh)
    (hg : IsLift (hbase := hbase) coordinate A g) :
    g = lift.hom := by
  letI : Algebra R Rsh := Algebra.restrictScalars R (Localization.AtPrime p) Rsh
  letI := CommAlgCat.Over.Target.Localization.algebra hbase A.obj
  letI : Algebra.Etale R A.obj.left := RingHom.etale_algebraMap.mp A.property
  let source (f : CommAlgCat.Over.Target.Localization.object hbase A.obj ⟶
      CommAlgCat.of (Localization.AtPrime p) Rsh) : A.obj.left →ₐ[R] Rsh :=
    { toRingHom := (ringHom hbase A f).comp
        (algebraMap A.obj.left
          (Localization.AtPrime (CommAlgCat.Over.Target.kernel A.obj)))
      commutes' := ringHom_apply_base hbase A f }
  have hres := (isLift_iff_residue hbase coordinate A g).mp hg
  have hlift := (isLift_iff_residue hbase coordinate A lift.hom).mp
    (spec hbase coordinate A lift)
  have he : source g = source lift.hom := by
    apply etaleHom_ext
    intro a
    apply coordinate.equiv.injective
    exact (DFunLike.congr_fun hres
      (algebraMap A.obj.left
        (Localization.AtPrime (CommAlgCat.Over.Target.kernel A.obj)) a)).trans
      (DFunLike.congr_fun hlift _).symm
  apply CommAlgCat.hom_ext
  apply AlgHom.coe_ringHom_injective
  exact IsLocalization.ringHom_ext (CommAlgCat.Over.Target.kernel A.obj).primeCompl
    (congrArg AlgHom.toRingHom he)

end Lift

/-- The localized pointed-etale lifting theorem for a chosen strict
henselization. -/
@[stacks 04GW "unique localized pointed-etale lift"]
theorem existsUnique_lift
    {Rsh : Type v} [CommRing Rsh]
    [Algebra (Localization.AtPrime p) Rsh]
    [IsStrictHenselizationOf (Localization.AtPrime p) Rsh]
    (coordinate : Coordinate (R := R) (K := K) hbase Rsh)
    (A : CommAlgCat.Over.Etale.category R K) :
    ∃! f : CommAlgCat.Over.Target.Localization.object hbase A.obj ⟶
      CommAlgCat.of (Localization.AtPrime p) Rsh,
      IsLift (hbase := hbase) coordinate A f := by
  letI : Algebra R Rsh := Algebra.restrictScalars R (Localization.AtPrime p) Rsh
  letI : IsScalarTower R (Localization.AtPrime p) Rsh := .of_algebraMap_eq' rfl
  letI : Algebra.Etale R A.obj.left := RingHom.etale_algebraMap.mp A.property
  let τ : A.obj.left →ₐ[R] ResidueField Rsh :=
    { toRingHom := coordinate.equiv.symm.toRingHom.comp
        (CommAlgCat.Over.Target.map A.obj)
      commutes' := fun r => by
        apply coordinate.equiv.injective
        change coordinate.equiv (coordinate.equiv.symm _) =
          coordinate.equiv (residue Rsh
            (algebraMap (Localization.AtPrime p) Rsh
              (algebraMap R (Localization.AtPrime p) r)))
        rw [RingEquiv.apply_symm_apply, Coordinate.equiv_apply_residue_base hbase coordinate]
        exact A.obj.hom.hom.commutes r }
  obtain ⟨f₀, hf₀⟩ := exists_etale_residue_lift τ
  have hpoint (a : A.obj.left) :
      coordinate.equiv (residue Rsh (f₀ a)) = CommAlgCat.Over.Target.map A.obj a := by
    rw [hf₀]
    exact coordinate.equiv.apply_symm_apply _
  have hunit (s : (CommAlgCat.Over.Target.kernel A.obj).primeCompl) : IsUnit (f₀ s) := by
    apply (residue_ne_zero_iff_isUnit _).mp
    intro hz
    apply s.property
    change CommAlgCat.Over.Target.map A.obj s = 0
    rw [← hpoint, hz, map_zero]
  let F : Localization.AtPrime (CommAlgCat.Over.Target.kernel A.obj) →+* Rsh :=
    IsLocalization.lift (M := (CommAlgCat.Over.Target.kernel A.obj).primeCompl) hunit
  have hcomm : F.comp (CommAlgCat.Over.Target.Localization.map hbase A.obj) =
      algebraMap (Localization.AtPrime p) Rsh := by
    apply IsLocalization.ringHom_ext p.primeCompl
    apply RingHom.ext
    intro r
    change F (Localization.localRingHom p (CommAlgCat.Over.Target.kernel A.obj)
      (algebraMap R A.obj.left) _ (algebraMap R (Localization.AtPrime p) r)) = _
    rw [Localization.localRingHom_to_map]
    change IsLocalization.lift hunit
      (algebraMap A.obj.left
        (Localization.AtPrime (CommAlgCat.Over.Target.kernel A.obj))
        (algebraMap R A.obj.left r)) = _
    rw [IsLocalization.lift_eq]
    exact f₀.commutes r
  letI := CommAlgCat.Over.Target.Localization.algebra hbase A.obj
  let f : CommAlgCat.Over.Target.Localization.object hbase A.obj ⟶
      CommAlgCat.of (Localization.AtPrime p) Rsh :=
    CommAlgCat.ofHom
      { toRingHom := F
        commutes' := fun r => DFunLike.congr_fun hcomm r }
  have hf : IsLift (hbase := hbase) coordinate A f := by
    apply (isLift_iff_residue hbase coordinate A f).mpr
    apply IsLocalization.ringHom_ext (CommAlgCat.Over.Target.kernel A.obj).primeCompl
    apply RingHom.ext
    intro a
    change coordinate.equiv (residue Rsh (IsLocalization.lift hunit
      (algebraMap A.obj.left
        (Localization.AtPrime (CommAlgCat.Over.Target.kernel A.obj)) a))) =
      (Ideal.ResidueField.lift (CommAlgCat.Over.Target.kernel A.obj)
        (CommAlgCat.Over.Target.map A.obj) le_rfl
        (fun a ha => isUnit_iff_ne_zero.mpr ha))
        (algebraMap A.obj.left (CommAlgCat.Over.Target.kernel A.obj).ResidueField a)
    rw [IsLocalization.lift_eq, Ideal.ResidueField.lift_algebraMap]
    exact hpoint a
  obtain ⟨hq, hr⟩ := hf
  exact ⟨f, ⟨hq, hr⟩, fun g hg =>
    Lift.unique hbase coordinate A ⟨f, hq, hr⟩ g hg⟩

/-! ### The localized presentation -/

/-- A natural family of chosen residue-compatible lifts of all pointed-etale
objects.  This is the explicit data owner for a presentation; it does not
hide a Classical.choose witness behind a public non-Prop definition. -/
@[stacks 04GW "pointed-etale strict-henselization presentation data"]
structure Presentation
    {Rsh : Type v} [CommRing Rsh]
    [Algebra (Localization.AtPrime p) Rsh]
    [IsStrictHenselizationOf (Localization.AtPrime p) Rsh]
    (coordinate : Coordinate (R := R) (K := K) hbase Rsh) where
  /-- The selected residue-compatible lift at each pointed-etale object. -/
  lift : ∀ A : CommAlgCat.Over.Etale.category R K,
    Lift (hbase := hbase) coordinate A
  /-- Naturality of the selected lifts along pointed-etale morphisms. -/
  naturality : ∀ {A B : CommAlgCat.Over.Etale.category R K} (f : A ⟶ B),
    CommAlgCat.Over.Target.Localization.morphism hbase f.hom ≫ (lift B).hom =
      (lift A).hom

namespace Presentation

variable {Rsh : Type v} [CommRing Rsh]
variable [Algebra (Localization.AtPrime p) Rsh]
variable [IsStrictHenselizationOf (Localization.AtPrime p) Rsh]
variable (coordinate : Coordinate (R := R) (K := K) hbase Rsh)

/-- The naturality field of a presentation in the precise form required by its
localized cocone. -/
@[stacks 04GW "cocone naturality of pointed-etale lifts"]
theorem cocone_naturality
    (presentation : Presentation (hbase := hbase) coordinate)
    {A B : CommAlgCat.Over.Etale.category R K} (f : A ⟶ B) :
    (CommAlgCat.Over.Etale.Localization.diagram hbase).map f ≫
        (presentation.lift B).hom =
      (presentation.lift A).hom ≫
        ((Functor.const (CommAlgCat.Over.Etale.category R K)).obj
          (CommAlgCat.of (Localization.AtPrime p) Rsh)).map f := by
  change CommAlgCat.Over.Target.Localization.morphism hbase f.hom ≫
      (presentation.lift B).hom = (presentation.lift A).hom ≫ 𝟙 _
  simpa using presentation.naturality f

/-- The localized cocone determined by a natural family of residue-compatible
lifts. -/
@[stacks 04GW "localized pointed-etale strict-henselization cocone"]
noncomputable def cocone
    (presentation : Presentation (hbase := hbase) coordinate) :
    Cocone (CommAlgCat.Over.Etale.Localization.diagram hbase) where
  pt := CommAlgCat.of (Localization.AtPrime p) Rsh
  ι :=
    { app := fun A => (presentation.lift A).hom
      naturality := fun {A B} f =>
        cocone_naturality (hbase := hbase) coordinate presentation
          (A := A) (B := B) f }

/-- The localized pointed-etale cocone admits a colimit witness.  This is
stated propositionally so the shared interface does not manufacture the
non-Prop `IsColimit` data from a deferred proof.  The base ring must fit the
carrier universe of the pointed-etale category. -/
@[stacks 04GW "localized pointed-etale strict-henselization colimit"]
theorem isColimit [Small.{v} R]
    (presentation : Presentation (hbase := hbase) coordinate) :
    Nonempty (IsColimit (cocone (hbase := hbase) coordinate presentation)) := sorry

/-! ### The source presentation -/

/-- The `R`-algebra structure on a strict henselization of `Rₚ`, obtained by
restriction along `R → Rₚ`.  It is a named value rather than a global
instance because it competes with any independently supplied `R`-algebra
structure on the same carrier. -/
@[stacks 04GW "source algebra of a pointed-etale presentation"]
noncomputable abbrev sourceAlgebra :
    Algebra R Rsh :=
  Algebra.restrictScalars R (Localization.AtPrime p) Rsh

/-- The target strict henselization regarded as an object of `CommAlgCat R`
via `sourceAlgebra`. -/
@[stacks 04GW "source object of a pointed-etale presentation"]
noncomputable abbrev sourceObject :
    CommAlgCat R :=
  letI : Algebra R Rsh := sourceAlgebra (R := R) (p := p) (Rsh := Rsh)
  CommAlgCat.of R Rsh

/-- The source-to-localization composite attached to a chosen localized
pointed-etale lift commutes with the restricted `R`-algebra structures. -/
@[stacks 04GW "source map algebra compatibility"]
theorem sourceMap_commutes
    (presentation : Presentation (hbase := hbase) coordinate)
    (A : CommAlgCat.Over.Etale.category R K) (r : R) :
    (ringHom hbase A (presentation.lift A).hom)
        (algebraMap A.obj.left
          (Localization.AtPrime (CommAlgCat.Over.Target.kernel A.obj))
          (algebraMap R A.obj.left r)) =
      ((algebraMap (Localization.AtPrime p) Rsh).comp
        (algebraMap R (Localization.AtPrime p))) r := by
  exact ringHom_apply_base hbase A (presentation.lift A).hom r

/-- The canonical map from a source pointed-etale algebra to the chosen
strict henselization, obtained by composing its localization map with the
presentation lift. -/
@[stacks 04GW "source map of a pointed-etale presentation"]
noncomputable def sourceMap
    (presentation : Presentation (hbase := hbase) coordinate)
    (A : CommAlgCat.Over.Etale.category R K) :
    (CommAlgCat.Over.Etale.diagram R K).obj A ⟶
      sourceObject (R := R) (p := p) (Rsh := Rsh) :=
  letI : Algebra R Rsh := sourceAlgebra (R := R) (p := p) (Rsh := Rsh)
  CommAlgCat.ofHom {
    toRingHom :=
      (ringHom hbase A (presentation.lift A).hom).comp
        (algebraMap A.obj.left
          (Localization.AtPrime (CommAlgCat.Over.Target.kernel A.obj)))
    commutes' := sourceMap_commutes (hbase := hbase) coordinate presentation A }

/-- The source maps of a presentation are natural in pointed-etale
morphisms. -/
@[stacks 04GW "source map naturality of a pointed-etale presentation"]
theorem sourceMap_naturality
    (presentation : Presentation (hbase := hbase) coordinate)
    {A B : CommAlgCat.Over.Etale.category R K} (f : A ⟶ B) :
    (CommAlgCat.Over.Etale.diagram R K).map f ≫
        sourceMap (hbase := hbase) coordinate presentation B =
      sourceMap (hbase := hbase) coordinate presentation A := by
  letI : Algebra R Rsh := sourceAlgebra (R := R) (p := p) (Rsh := Rsh)
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro x
  change (ringHom hbase B (presentation.lift B).hom)
      (algebraMap B.obj.left
        (Localization.AtPrime (CommAlgCat.Over.Target.kernel B.obj))
        (CommAlgCat.Over.Target.hom f.hom x)) =
    (ringHom hbase A (presentation.lift A).hom)
      (algebraMap A.obj.left
        (Localization.AtPrime (CommAlgCat.Over.Target.kernel A.obj)) x)
  have h := congrArg
    (fun g : CommAlgCat.Over.Target.Localization.object hbase A.obj ⟶
        CommAlgCat.of (Localization.AtPrime p) Rsh =>
      ringHom hbase A g
        (algebraMap A.obj.left
          (Localization.AtPrime (CommAlgCat.Over.Target.kernel A.obj)) x))
    (presentation.naturality f)
  change (ringHom hbase B (presentation.lift B).hom)
      ((CommAlgCat.Over.Target.Localization.hom f.hom)
        (algebraMap A.obj.left
          (Localization.AtPrime (CommAlgCat.Over.Target.kernel A.obj)) x)) =
    (ringHom hbase A (presentation.lift A).hom)
      (algebraMap A.obj.left
        (Localization.AtPrime (CommAlgCat.Over.Target.kernel A.obj)) x) at h
  simpa only [CommAlgCat.Over.Target.Localization.hom,
    Localization.localRingHom_to_map] using h

/-- The cocone from the source pointed-etale diagram to the selected strict
henselization. -/
@[stacks 04GW "source pointed-etale strict-henselization cocone"]
noncomputable def sourceCocone
    (presentation : Presentation (hbase := hbase) coordinate) :
    Cocone (CommAlgCat.Over.Etale.diagram R K) where
  pt := sourceObject (R := R) (p := p) (Rsh := Rsh)
  ι :=
    { app := fun A => sourceMap (hbase := hbase) coordinate presentation A
      naturality := fun {A B} f =>
        sourceMap_naturality (hbase := hbase) coordinate presentation
          (A := A) (B := B) f }

/-- The source pointed-etale cocone admits a colimit witness.  As with the
localized presentation, the witness is stated propositionally rather than
manufactured as deferred non-Prop data.  The base ring must fit the carrier
universe of the pointed-etale category. -/
@[stacks 04GW "source pointed-etale strict-henselization colimit"]
theorem sourceIsColimit [Small.{v} R]
    (presentation : Presentation (hbase := hbase) coordinate) :
    Nonempty (IsColimit (sourceCocone (hbase := hbase) coordinate presentation)) := sorry

end Presentation

/-- Existence of presentation data is stated propositionally; the shared layer
does not manufacture a public non-Prop witness from Classical.choose. -/
@[stacks 04GW "existence of a pointed-etale strict-henselization presentation"]
theorem exists_presentation
    {Rsh : Type v} [CommRing Rsh]
    [Algebra (Localization.AtPrime p) Rsh]
    [IsStrictHenselizationOf (Localization.AtPrime p) Rsh]
    (coordinate : Coordinate (R := R) (K := K) hbase Rsh) :
    Nonempty (Presentation (hbase := hbase) coordinate) := by
  classical
  have hlift (A : CommAlgCat.Over.Etale.category R K) :
      Nonempty (Lift (hbase := hbase) coordinate A) := by
    obtain ⟨f, ⟨hq, hr⟩, _⟩ := existsUnique_lift hbase coordinate A
    exact ⟨⟨f, hq, hr⟩⟩
  let lifts (A : CommAlgCat.Over.Etale.category R K) := Classical.choice (hlift A)
  refine ⟨{ lift := lifts, naturality := ?_ }⟩
  intro A B f
  apply Lift.unique hbase coordinate A (lifts A)
  apply (isLift_iff_residue hbase coordinate A _).mpr
  have hB := (isLift_iff_residue hbase coordinate B (lifts B).hom).mp
    (Lift.spec hbase coordinate B (lifts B))
  apply IsLocalization.ringHom_ext (CommAlgCat.Over.Target.kernel A.obj).primeCompl
  apply RingHom.ext
  intro a
  change coordinate.equiv (residue Rsh
      (ringHom hbase B (lifts B).hom
        (Localization.localRingHom (CommAlgCat.Over.Target.kernel A.obj)
          (CommAlgCat.Over.Target.kernel B.obj) (CommAlgCat.Over.Target.hom f.hom)
          (CommAlgCat.Over.Target.kernel_comap f.hom)
          (algebraMap A.obj.left
            (Localization.AtPrime (CommAlgCat.Over.Target.kernel A.obj)) a)))) =
    (Ideal.ResidueField.lift (CommAlgCat.Over.Target.kernel A.obj)
      (CommAlgCat.Over.Target.map A.obj) le_rfl
      (fun a ha => isUnit_iff_ne_zero.mpr ha))
      (algebraMap A.obj.left (CommAlgCat.Over.Target.kernel A.obj).ResidueField a)
  rw [Localization.localRingHom_to_map, Ideal.ResidueField.lift_algebraMap]
  have h := DFunLike.congr_fun hB
    (algebraMap B.obj.left
      (Localization.AtPrime (CommAlgCat.Over.Target.kernel B.obj))
      (CommAlgCat.Over.Target.hom f.hom a))
  change coordinate.equiv (residue Rsh
      (ringHom hbase B (lifts B).hom
        (algebraMap B.obj.left
          (Localization.AtPrime (CommAlgCat.Over.Target.kernel B.obj))
          (CommAlgCat.Over.Target.hom f.hom a)))) =
    (Ideal.ResidueField.lift (CommAlgCat.Over.Target.kernel B.obj)
      (CommAlgCat.Over.Target.map B.obj) le_rfl
      (fun b hb => isUnit_iff_ne_zero.mpr hb))
      (algebraMap B.obj.left (CommAlgCat.Over.Target.kernel B.obj).ResidueField
        (CommAlgCat.Over.Target.hom f.hom a)) at h
  rw [Ideal.ResidueField.lift_algebraMap] at h
  exact h.trans (congrArg
    (fun k : A.obj.left ⟶ CommAlgCat.of R K => k.hom a) f.hom.w)

end

end IsStrictHenselizationOf.PointedEtale
