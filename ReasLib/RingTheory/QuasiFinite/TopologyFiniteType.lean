/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.QuasiFinite.LocalizationOfQuasiFinite
public import Mathlib.Algebra.Field.ULift
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic

@[expose] public section

universe u

noncomputable section

open PowerSeries

namespace PowerSeries.LaurentConstant

/-- The subring `A` of `PowerSeries (LaurentSeries k)` consisting of series whose constant
term lies in the image of `k →+* LaurentSeries k`. -/
def baseSubring (k : Type u) [Field k] : Subring (PowerSeries (LaurentSeries k)) :=
  (algebraMap k (LaurentSeries k)).range.comap constantCoeff

/-- The subring `C` of `PowerSeries (LaurentSeries k)` consisting of series whose constant
term lies in the image of `Polynomial k →+* LaurentSeries k`. -/
def polynomialSubring (k : Type u) [Field k] : Subring (PowerSeries (LaurentSeries k)) :=
  (algebraMap (Polynomial k) (LaurentSeries k)).range.comap constantCoeff

/-- Membership in `baseSubring k` is equivalent to the constant coefficient lying in the
image of `k`. -/
theorem baseSubring_mem_iff {k : Type u} [Field k] {f : PowerSeries (LaurentSeries k)} :
    f ∈ baseSubring k ↔ constantCoeff f ∈ (algebraMap k (LaurentSeries k)).range := Iff.rfl

/-- Membership in `polynomialSubring k` is equivalent to the constant coefficient lying in
the image of `Polynomial k`. -/
theorem polynomialSubring_mem_iff {k : Type u} [Field k] {f : PowerSeries (LaurentSeries k)} :
    f ∈ polynomialSubring k ↔
      constantCoeff f ∈ (algebraMap (Polynomial k) (LaurentSeries k)).range := Iff.rfl

/-- The constant-term subring `A` is contained in the polynomial-constant subring `C`. -/
theorem baseSubring_le_polynomialSubring (k : Type u) [Field k] :
    baseSubring k ≤ polynomialSubring k := by
  intro f hf
  rcases baseSubring_mem_iff.mp hf with ⟨a, ha⟩
  refine polynomialSubring_mem_iff.mpr ⟨Polynomial.C a, ?_⟩
  rw [Polynomial.C_eq_algebraMap]
  simpa [LaurentSeries.algebraMap_apply] using ha

/-- The constant series whose constant term is the image of `Polynomial.X`, as an element
of `polynomialSubring k`. -/
def generator (k : Type u) [Field k] : polynomialSubring k :=
  ⟨C (algebraMap (Polynomial k) (LaurentSeries k) Polynomial.X),
    Subring.mem_comap.mpr
      ((constantCoeff_C (algebraMap (Polynomial k) (LaurentSeries k) Polynomial.X)).symm ▸
        RingHom.mem_range_self _ Polynomial.X)⟩

/-- The generator of `polynomialSubring k` over `baseSubring k` lies in `polynomialSubring k`. -/
theorem generator_mem (k : Type u) [Field k] : (generator k : PowerSeries (LaurentSeries k)) ∈
    polynomialSubring k := (generator k).property

/-- The inclusion `A →+* C` of constant-term subrings. -/
def toIntermediate (k : Type u) [Field k] : baseSubring k →+* polynomialSubring k :=
  Subring.inclusion (by
    intro f hf
    change constantCoeff f ∈ (algebraMap k (LaurentSeries k)).range at hf
    change constantCoeff f ∈ (algebraMap (Polynomial k) (LaurentSeries k)).range
    rcases hf with ⟨x, hx⟩
    refine ⟨Polynomial.C x, ?_⟩
    rw [Polynomial.C_eq_algebraMap]
    simpa [LaurentSeries.algebraMap_apply] using hx)

/-- The inclusion `A →+* C` is of finite type. -/
theorem toIntermediate_finiteType (k : Type u) [Field k] :
    (toIntermediate k).FiniteType := by
  letI := (toIntermediate k).toAlgebra
  change Algebra.FiniteType (baseSubring k) (polynomialSubring k)
  constructor
  refine Subalgebra.fg_def.mpr ⟨{generator k}, Set.finite_singleton _, ?_⟩
  let S := Algebra.adjoin (baseSubring k) ({generator k} : Set (polynomialSubring k))
  let j : Polynomial k →+* polynomialSubring k :=
    (C.comp (algebraMap (Polynomial k) (LaurentSeries k))).codRestrict
      (polynomialSubring k) (fun p => by
        change constantCoeff (C (algebraMap (Polynomial k) (LaurentSeries k) p)) ∈
          (algebraMap (Polynomial k) (LaurentSeries k)).range
        rw [constantCoeff_C]
        exact RingHom.mem_range_self _ p)
  have hbase (g : PowerSeries (LaurentSeries k)) (hg : g ∈ baseSubring k) :
      (⟨g, baseSubring_le_polynomialSubring k hg⟩ : polynomialSubring k) ∈ S :=
    S.algebraMap_mem (⟨g, hg⟩ : baseSubring k)
  have hj (p : Polynomial k) : j p ∈ S := by
    induction p using Polynomial.induction_on with
    | C a =>
        apply hbase
        change constantCoeff (C (algebraMap (Polynomial k) (LaurentSeries k)
          (Polynomial.C a))) ∈ (algebraMap k (LaurentSeries k)).range
        rw [constantCoeff_C]
        refine ⟨a, ?_⟩
        rw [Polynomial.C_eq_algebraMap]
        simp [LaurentSeries.algebraMap_apply]
    | add p q hp hq => simpa only [map_add] using S.add_mem hp hq
    | monomial n a h =>
        rw [pow_succ, ← mul_assoc, map_mul]
        exact S.mul_mem h (Algebra.subset_adjoin (Set.mem_singleton _))
  apply top_unique
  intro f _
  rcases f.property with ⟨p, hp⟩
  have hdiff : (f : PowerSeries (LaurentSeries k)) - (j p : PowerSeries (LaurentSeries k)) ∈
      baseSubring k := by
    change constantCoeff ((f : PowerSeries (LaurentSeries k)) -
      C (algebraMap (Polynomial k) (LaurentSeries k) p)) ∈
        (algebraMap k (LaurentSeries k)).range
    rw [map_sub, constantCoeff_C, ← hp, sub_self]
    exact ⟨0, map_zero _⟩
  have h := S.add_mem (hbase _ hdiff) (hj p)
  convert h using 1
  apply Subtype.ext
  exact (sub_add_cancel _ _).symm

/-- The prime `p ⊂ C` of series with vanishing constant term. -/
def positiveDegreeIdeal (k : Type u) [Field k] : Ideal (polynomialSubring k) :=
  RingHom.ker (constantCoeff.comp (polynomialSubring k).subtype)

/-- The ideal `m_C = yC + p` at which `C` is localized. -/
def localizationIdeal (k : Type u) [Field k] : Ideal (polynomialSubring k) :=
  Ideal.span {generator k} ⊔ positiveDegreeIdeal k

/-- Membership in `m_C` means that the polynomial constant term vanishes at zero. -/
theorem mem_localizationIdeal_iff {k : Type u} [Field k] (f : polynomialSubring k) :
    f ∈ localizationIdeal k ↔ ∃ p : Polynomial k,
      algebraMap (Polynomial k) (LaurentSeries k) p =
        constantCoeff (f : PowerSeries (LaurentSeries k)) ∧ p.coeff 0 = 0 := by
  constructor
  · intro hf
    rcases Submodule.mem_sup.mp hf with ⟨a, ha, b, hb, hab⟩
    rcases Ideal.mem_span_singleton.mp ha with ⟨r, rfl⟩
    rcases r.property with ⟨p, hp⟩
    have hb' : constantCoeff (b : PowerSeries (LaurentSeries k)) = 0 := hb
    refine ⟨Polynomial.X * p, ?_, by simp⟩
    rw [map_mul, hp, ← hab]
    simp [generator, hb']
  · rintro ⟨p, hp, hp0⟩
    obtain ⟨r, hr⟩ := Polynomial.X_dvd_iff.mpr hp0
    let s : polynomialSubring k :=
      ⟨C (algebraMap (Polynomial k) (LaurentSeries k) r), by
        change constantCoeff (C (algebraMap (Polynomial k) (LaurentSeries k) r)) ∈
          (algebraMap (Polynomial k) (LaurentSeries k)).range
        rw [constantCoeff_C]
        exact RingHom.mem_range_self _ r⟩
    have hprod : generator k * s ∈ localizationIdeal k :=
      Ideal.mem_sup_left (Ideal.mem_span_singleton.mpr ⟨s, rfl⟩)
    have hdiff : f - generator k * s ∈ positiveDegreeIdeal k := by
      change constantCoeff ((f : PowerSeries (LaurentSeries k)) -
        C (algebraMap (Polynomial k) (LaurentSeries k) Polynomial.X) *
          C (algebraMap (Polynomial k) (LaurentSeries k) r)) = 0
      rw [map_sub, map_mul, constantCoeff_C, constantCoeff_C, ← hp, hr, map_mul,
        sub_self]
    simpa only [add_sub_cancel] using
      (localizationIdeal k).add_mem hprod (Ideal.mem_sup_right hdiff)

/-- The ideal `m_C = yC + p` is prime. -/
instance instIsPrimeLocalizationIdeal (k : Type u) [Field k] :
    (localizationIdeal k).IsPrime := by
  have hinj : Function.Injective (algebraMap (Polynomial k) (LaurentSeries k)) :=
    Polynomial.algebraMap_hahnSeries_injective ℤ
  constructor
  · intro htop
    have hone : (1 : polynomialSubring k) ∈ localizationIdeal k := by
      rw [htop]
      trivial
    rcases (mem_localizationIdeal_iff 1).mp hone with ⟨p, hp, hp0⟩
    have hp1 : p = 1 := hinj (by simpa using hp)
    simpa [hp1] using hp0
  · intro f g hfg
    rcases f.property with ⟨p, hp⟩
    rcases g.property with ⟨q, hq⟩
    rcases (mem_localizationIdeal_iff (f * g)).mp hfg with ⟨r, hr, hr0⟩
    have hpq : p * q = r := hinj (by
      rw [map_mul, hp, hq]
      simpa only [Subring.coe_mul, map_mul] using hr.symm)
    have hzero : p.coeff 0 * q.coeff 0 = 0 := by
      rw [← Polynomial.mul_coeff_zero, hpq]
      exact hr0
    rcases mul_eq_zero.mp hzero with hp0 | hq0
    · exact Or.inl ((mem_localizationIdeal_iff f).mpr ⟨p, hp, hp0⟩)
    · exact Or.inr ((mem_localizationIdeal_iff g).mpr ⟨q, hq, hq0⟩)

/-- A series in `A` is a unit precisely when its constant term is nonzero. -/
theorem isUnit_baseSubring_iff {k : Type u} [Field k] (f : baseSubring k) :
    IsUnit f ↔ constantCoeff (f : PowerSeries (LaurentSeries k)) ≠ 0 := by
  constructor
  · intro hf
    exact (hf.map (constantCoeff.comp (baseSubring k).subtype)).ne_zero
  · intro hf
    rcases f.property with ⟨a, ha⟩
    refine isUnit_iff_exists_inv.mpr ⟨⟨(f : PowerSeries (LaurentSeries k))⁻¹, ?_⟩, ?_⟩
    · change constantCoeff (f : PowerSeries (LaurentSeries k))⁻¹ ∈
        (algebraMap k (LaurentSeries k)).range
      refine ⟨a⁻¹, ?_⟩
      simpa only [map_inv₀, constantCoeff_inv] using congrArg Inv.inv ha
    · apply Subtype.ext
      exact PowerSeries.mul_inv_cancel _ hf

/-- The constant-term subring `A` is a local ring. -/
instance instIsLocalRingBaseSubring (k : Type u) [Field k] :
    IsLocalRing (baseSubring k) where
  toNontrivial := inferInstance
  isUnit_or_isUnit_of_add_one {a b} hab := by
    by_cases ha : constantCoeff (a : PowerSeries (LaurentSeries k)) = 0
    · right
      apply (isUnit_baseSubring_iff b).mpr
      intro hb
      have h := congrArg (fun f : baseSubring k =>
        constantCoeff (f : PowerSeries (LaurentSeries k))) hab
      simpa [map_add, ha, hb] using h
    · exact Or.inl ((isUnit_baseSubring_iff a).mpr ha)

/-- The local homomorphism `A →+* C_{m_C}` obtained by including `A` into `C` and
localizing at `m_C`. -/
def toLocalization (k : Type u) [Field k] :
    baseSubring k →+* Localization.AtPrime (localizationIdeal k) :=
  (algebraMap (polynomialSubring k) (Localization.AtPrime (localizationIdeal k))).comp
    (toIntermediate k)

/-- The constructed map `A →+* C_{m_C}` is a local homomorphism. -/
instance instIsLocalHomToLocalization (k : Type u) [Field k] :
    IsLocalHom (toLocalization k) where
  map_nonunit f hf := by
    apply (isUnit_baseSubring_iff f).mpr
    intro hzero
    have hpos : toIntermediate k f ∈ positiveDegreeIdeal k := hzero
    have hmem : toIntermediate k f ∈ localizationIdeal k := Ideal.mem_sup_right hpos
    exact ((IsLocalization.AtPrime.isUnit_to_map_iff
      (Localization.AtPrime (localizationIdeal k)) (localizationIdeal k)
        (toIntermediate k f)).mp hf) hmem

/-- The canonical `A`-algebra structure on `C_{m_C}` induced by `toLocalization`. -/
instance instAlgebraToLocalization (k : Type u) [Field k] :
    Algebra (baseSubring k) (Localization.AtPrime (localizationIdeal k)) :=
  (toLocalization k).toAlgebra

/-- The constructed map `A →+* C_{m_C}` is essentially of finite type. -/
theorem toLocalization_essFiniteType (k : Type u) [Field k] :
    (toLocalization k).EssFiniteType := by
  letI := (toIntermediate k).toAlgebra
  letI : Algebra (polynomialSubring k) (Localization.AtPrime (localizationIdeal k)) :=
    inferInstance
  letI := (toLocalization k).toAlgebra
  letI := IsScalarTower.of_algebraMap_eq' (R := baseSubring k) (S := polynomialSubring k)
    (A := Localization.AtPrime (localizationIdeal k)) rfl
  haveI : Algebra.FiniteType (baseSubring k) (polynomialSubring k) :=
    toIntermediate_finiteType k
  change Algebra.EssFiniteType (baseSubring k) (Localization.AtPrime (localizationIdeal k))
  exact Algebra.EssFiniteType.comp (baseSubring k) (polynomialSubring k)
    (Localization.AtPrime (localizationIdeal k))

/-- The residue-field extension induced by `A →+* C_{m_C}` is finite. -/
theorem toLocalization_residueField_finite (k : Type u) [Field k] :
    (IsLocalRing.ResidueField.map (toLocalization k)).Finite := by
  let B := Localization.AtPrime (localizationIdeal k)
  let f := IsLocalRing.ResidueField.map (toLocalization k)
  have hconst (g : polynomialSubring k) : ∃ a : baseSubring k,
      IsLocalRing.residue B (algebraMap (polynomialSubring k) B g) =
        f (IsLocalRing.residue (baseSubring k) a) := by
    rcases g.property with ⟨p, hp⟩
    let a : baseSubring k :=
      ⟨C (algebraMap k (LaurentSeries k) (p.coeff 0)), by
        change constantCoeff (C (algebraMap k (LaurentSeries k) (p.coeff 0))) ∈
          (algebraMap k (LaurentSeries k)).range
        rw [constantCoeff_C]
        exact RingHom.mem_range_self _ _⟩
    have hC : algebraMap (Polynomial k) (LaurentSeries k) (Polynomial.C (p.coeff 0)) =
        algebraMap k (LaurentSeries k) (p.coeff 0) := by
      rw [Polynomial.C_eq_algebraMap]
      simp [LaurentSeries.algebraMap_apply]
    have hdiff : g - toIntermediate k a ∈ localizationIdeal k := by
      apply (mem_localizationIdeal_iff _).mpr
      refine ⟨p - Polynomial.C (p.coeff 0), ?_, by simp⟩
      change algebraMap (Polynomial k) (LaurentSeries k) (p - Polynomial.C (p.coeff 0)) =
        constantCoeff ((g : PowerSeries (LaurentSeries k)) -
          C (algebraMap k (LaurentSeries k) (p.coeff 0)))
      simp only [map_sub, constantCoeff_C, hC, hp]
    have hzero : IsLocalRing.residue B
        (algebraMap (polynomialSubring k) B (g - toIntermediate k a)) = 0 :=
      (IsLocalRing.residue_eq_zero_iff _).mpr
        ((IsLocalization.AtPrime.to_map_mem_maximal_iff B (localizationIdeal k) _).mpr hdiff)
    refine ⟨a, ?_⟩
    apply sub_eq_zero.mp
    simpa [f, toLocalization, map_sub] using hzero
  apply RingHom.Finite.of_surjective
  intro z
  obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective (R := B) z
  obtain ⟨r, s, rfl⟩ := IsLocalization.exists_mk'_eq (localizationIdeal k).primeCompl b
  obtain ⟨a, ha⟩ := hconst r
  obtain ⟨c, hc⟩ := hconst s
  refine ⟨IsLocalRing.residue (baseSubring k) a /
    IsLocalRing.residue (baseSubring k) c, ?_⟩
  change f _ = _
  rw [map_div₀, ← ha, ← hc]
  have hs : IsLocalRing.residue B (algebraMap (polynomialSubring k) B s) ≠ 0 :=
    (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr (IsLocalization.map_units B s)
  apply (div_eq_iff hs).mpr
  rw [← map_mul, IsLocalization.mk'_spec]

/-- The composite `A →+* (C_{m_C}) ⧸ q`. -/
def toLocalizationQuotient (k : Type u) [Field k]
    (q : Ideal (Localization.AtPrime (localizationIdeal k))) :
    baseSubring k →+* Localization.AtPrime (localizationIdeal k) ⧸ q :=
  algebraMap (baseSubring k) (Localization.AtPrime (localizationIdeal k) ⧸ q)

/-- `toLocalizationQuotient` is the composite of `toLocalization` with the quotient map. -/
theorem toLocalizationQuotient_eq_comp (k : Type u) [Field k]
    (q : Ideal (Localization.AtPrime (localizationIdeal k))) :
    toLocalizationQuotient k q = (Ideal.Quotient.mk q).comp (toLocalization k) := rfl

/-- For every prime of `C_{m_C}` other than the maximal ideal, the composite from `A` to
the quotient is not a localization of a quasi-finite ring map. -/
theorem toLocalization_not_isLocalizationOfQuasiFinite (k : Type u) [Field k]
    (q : Ideal (Localization.AtPrime (localizationIdeal k))) [q.IsPrime]
    (hq : q ≠ IsLocalRing.maximalIdeal (Localization.AtPrime (localizationIdeal k))) :
    ¬ Algebra.IsLocalizationOfQuasiFinite (baseSubring k)
        (Localization.AtPrime (localizationIdeal k) ⧸ q) := sorry

end PowerSeries.LaurentConstant

namespace RingHom

/-- There exist local domains `A` and `B` and a local homomorphism `f : A →+* B` which is
essentially of finite type with finite residue-field extension, while every nonmaximal prime
quotient of `B` is not a localization of a quasi-finite ring map from `A`. -/
theorem exists_local_essFiniteType_residueFinite_not_localization_quasiFinite :
    ∃ (A B : Type u) (_ : CommRing A) (_ : CommRing B) (_ : IsLocalRing A) (_ : IsLocalRing B)
      (_ : IsDomain A) (_ : IsDomain B) (f : A →+* B) (_ : IsLocalHom f),
      f.EssFiniteType ∧
        (IsLocalRing.ResidueField.map f).Finite ∧
        ∀ (q : Ideal B), q.IsPrime → q ≠ IsLocalRing.maximalIdeal B →
          ¬ ((Ideal.Quotient.mk q).comp f).IsLocalizationOfQuasiFinite := by
  have h (K : Type u) [Field K]
      (q : Ideal (Localization.AtPrime (PowerSeries.LaurentConstant.localizationIdeal K)))
      [q.IsPrime]
      (hne : q ≠ IsLocalRing.maximalIdeal
        (Localization.AtPrime (PowerSeries.LaurentConstant.localizationIdeal K))) :
      ¬ ((Ideal.Quotient.mk q).comp
        (PowerSeries.LaurentConstant.toLocalization K)).IsLocalizationOfQuasiFinite := by
    have halg : ((Ideal.Quotient.mk q).comp
        (PowerSeries.LaurentConstant.toLocalization K)).toAlgebra =
        (inferInstance : Algebra (PowerSeries.LaurentConstant.baseSubring K)
          (Localization.AtPrime (PowerSeries.LaurentConstant.localizationIdeal K) ⧸ q)) := by
      apply Algebra.algebra_ext
      intro a
      rfl
    unfold RingHom.IsLocalizationOfQuasiFinite
    rw [halg]
    exact PowerSeries.LaurentConstant.toLocalization_not_isLocalizationOfQuasiFinite K q hne
  let k := ULift.{u} ℚ
  refine ⟨PowerSeries.LaurentConstant.baseSubring k,
    Localization.AtPrime (PowerSeries.LaurentConstant.localizationIdeal k),
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    PowerSeries.LaurentConstant.toLocalization k, inferInstance,
    PowerSeries.LaurentConstant.toLocalization_essFiniteType k,
    PowerSeries.LaurentConstant.toLocalization_residueField_finite k, ?_⟩
  intro q hq hne
  letI := hq
  exact h k q hne

end RingHom
