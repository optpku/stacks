/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.QuasiFinite.LocalizationOfQuasiFinite
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
    f ∈ baseSubring k ↔ constantCoeff f ∈ (algebraMap k (LaurentSeries k)).range := sorry

/-- Membership in `polynomialSubring k` is equivalent to the constant coefficient lying in
the image of `Polynomial k`. -/
theorem polynomialSubring_mem_iff {k : Type u} [Field k] {f : PowerSeries (LaurentSeries k)} :
    f ∈ polynomialSubring k ↔
      constantCoeff f ∈ (algebraMap (Polynomial k) (LaurentSeries k)).range := sorry

/-- The constant-term subring `A` is contained in the polynomial-constant subring `C`. -/
theorem baseSubring_le_polynomialSubring (k : Type u) [Field k] :
    baseSubring k ≤ polynomialSubring k := sorry

/-- The constant series whose constant term is the image of `Polynomial.X`, as an element
of `polynomialSubring k`. -/
def generator (k : Type u) [Field k] : polynomialSubring k :=
  ⟨C (algebraMap (Polynomial k) (LaurentSeries k) Polynomial.X),
    Subring.mem_comap.mpr
      ((constantCoeff_C (algebraMap (Polynomial k) (LaurentSeries k) Polynomial.X)).symm ▸
        RingHom.mem_range_self _ Polynomial.X)⟩

/-- The generator of `polynomialSubring k` over `baseSubring k` lies in `polynomialSubring k`. -/
theorem generator_mem (k : Type u) [Field k] : (generator k : PowerSeries (LaurentSeries k)) ∈
    polynomialSubring k := sorry

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
    (toIntermediate k).FiniteType := sorry

/-- The prime `p ⊂ C` of series with vanishing constant term. -/
def positiveDegreeIdeal (k : Type u) [Field k] : Ideal (polynomialSubring k) :=
  RingHom.ker (constantCoeff.comp (polynomialSubring k).subtype)

/-- The ideal `m_C = yC + p` at which `C` is localized. -/
def localizationIdeal (k : Type u) [Field k] : Ideal (polynomialSubring k) :=
  Ideal.span {generator k} ⊔ positiveDegreeIdeal k

/-- The ideal `m_C = yC + p` is prime. -/
instance instIsPrimeLocalizationIdeal (k : Type u) [Field k] :
    (localizationIdeal k).IsPrime := sorry

/-- The constant-term subring `A` is a local ring. -/
instance instIsLocalRingBaseSubring (k : Type u) [Field k] :
    IsLocalRing (baseSubring k) := sorry

/-- The local homomorphism `A →+* C_{m_C}` obtained by including `A` into `C` and
localizing at `m_C`. -/
def toLocalization (k : Type u) [Field k] :
    baseSubring k →+* Localization.AtPrime (localizationIdeal k) :=
  (algebraMap (polynomialSubring k) (Localization.AtPrime (localizationIdeal k))).comp
    (toIntermediate k)

/-- The constructed map `A →+* C_{m_C}` is a local homomorphism. -/
instance instIsLocalHomToLocalization (k : Type u) [Field k] :
    IsLocalHom (toLocalization k) := sorry

/-- The canonical `A`-algebra structure on `C_{m_C}` induced by `toLocalization`. -/
instance instAlgebraToLocalization (k : Type u) [Field k] :
    Algebra (baseSubring k) (Localization.AtPrime (localizationIdeal k)) :=
  (toLocalization k).toAlgebra

/-- The constructed map `A →+* C_{m_C}` is essentially of finite type. -/
theorem toLocalization_essFiniteType (k : Type u) [Field k] :
    (toLocalization k).EssFiniteType := sorry

/-- The residue-field extension induced by `A →+* C_{m_C}` is finite. -/
theorem toLocalization_residueField_finite (k : Type u) [Field k] :
    (IsLocalRing.ResidueField.map (toLocalization k)).Finite := sorry

/-- The composite `A →+* (C_{m_C}) ⧸ q`. -/
def toLocalizationQuotient (k : Type u) [Field k]
    (q : Ideal (Localization.AtPrime (localizationIdeal k))) :
    baseSubring k →+* Localization.AtPrime (localizationIdeal k) ⧸ q :=
  algebraMap (baseSubring k) (Localization.AtPrime (localizationIdeal k) ⧸ q)

/-- `toLocalizationQuotient` is the composite of `toLocalization` with the quotient map. -/
theorem toLocalizationQuotient_eq_comp (k : Type u) [Field k]
    (q : Ideal (Localization.AtPrime (localizationIdeal k))) :
    toLocalizationQuotient k q = (Ideal.Quotient.mk q).comp (toLocalization k) := sorry

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
          ¬ ((Ideal.Quotient.mk q).comp f).IsLocalizationOfQuasiFinite := sorry

end RingHom
