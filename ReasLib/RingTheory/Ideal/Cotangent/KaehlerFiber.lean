/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.Localization.Submodule
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import ReasLib.RingTheory.Ideal.Cotangent.Localization
public import ReasLib.RingTheory.LocalRing.ResidueField.MaximalIdeal
public import ReasLib.RingTheory.Kaehler.Conormal

/-!
# Closed-point Kähler fibers

This leaf owns the comparison between the Kähler fiber and the cotangent
module at a maximal ideal.  The canonical owner uses the residue field and a
separable field extension.  The quotient form is the source-facing closed-point
specialization over an algebraically closed field.

@stack 00TR
-/

@[expose] public section

open scoped TensorProduct
open KaehlerDifferential

universe u v

namespace Ideal.Cotangent

variable {k : Type u} {S : Type v}
variable [Field k] [CommRing S] [Algebra k S]

/-- If the residue field at a maximal ideal is separable over the base field,
the conormal sequence identifies the scalar-extended cotangent module with the
Kähler fiber.  This is the canonical, field-valued owner behind the closed-point
finrank statements below. -/
noncomputable def kaehlerFiberEquiv (m : Ideal S) [m.IsMaximal]
    [Algebra.IsSeparable k m.ResidueField] :
    m.ResidueField ⊗[S ⧸ m] m.Cotangent ≃ₗ[m.ResidueField]
      m.ResidueField ⊗[S] Ω[S⁄k] := by
  classical
  let κm := m.ResidueField
  let V := κm ⊗[S] Ω[S⁄k]
  let eKer : m.Cotangent ≃ₗ[S]
      (RingHom.ker (algebraMap S κm)).Cotangent :=
    Ideal.Cotangent.equivOfEq _ _ (Ideal.ker_algebraMap_residueField m).symm
  let conormal : m.Cotangent →ₗ[S] V :=
    (KaehlerDifferential.kerCotangentToTensor k S κm).comp eKer.toLinearMap
  have hsurj : Function.Surjective (algebraMap S κm) :=
    m.algebraMap_residueField_surjective
  letI : Algebra.FormallyEtale k κm := Algebra.FormallyEtale.of_isSeparable k κm
  have hconormal : Function.Bijective conormal := by
    have hinjective : Function.Injective
        (KaehlerDifferential.kerCotangentToTensor k S κm) :=
      KaehlerDifferential.Conormal.injective_of_formallySmooth hsurj
    have hsurjective : Function.Surjective
        (KaehlerDifferential.kerCotangentToTensor k S κm) := by
      rw [← LinearMap.range_eq_top,
        KaehlerDifferential.range_kerCotangentToTensor k S κm hsurj]
      apply top_unique
      intro x _
      change KaehlerDifferential.mapBaseChange k S κm x = 0
      exact Subsingleton.elim _ _
    exact ⟨hinjective.comp eKer.injective, hsurjective.comp eKer.surjective⟩
  let conormalQuotient : m.Cotangent →ₗ[S ⧸ m] V :=
    conormal.extendScalarsOfSurjective Ideal.Quotient.mk_surjective
  have hconormalQuotient : Function.Bijective conormalQuotient := by
    constructor
    · intro x y hxy
      apply hconormal.injective
      exact hxy
    · intro y
      obtain ⟨x, hx⟩ := hconormal.surjective y
      exact ⟨x, hx⟩
  letI : Algebra.IsEpi (S ⧸ m) κm :=
    Algebra.isEpi_of_surjective_algebraMap _ _
      m.bijective_algebraMap_quotient_residueField.surjective
  exact
    (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl κm κm)
      (LinearEquiv.ofBijective conormalQuotient hconormalQuotient)).trans
        (TensorProduct.lid' (S ⧸ m) κm V)

/-- The canonical residue-field form of the Kähler-fiber/cotangent comparison. -/
theorem finrank_residueField_kaehlerFiber_eq_cotangent
    (m : Ideal S) [m.IsMaximal] [Algebra.IsSeparable k m.ResidueField] :
    Module.finrank m.ResidueField (m.ResidueField ⊗[S] Ω[S⁄k]) =
      Module.finrank m.ResidueField (m.ResidueField ⊗[S ⧸ m] m.Cotangent) := by
  exact (kaehlerFiberEquiv (k := k) m).finrank_eq.symm

/-- At a maximal ideal with separable residue field, the Kähler fiber and the
cotangent space of the prime localization have the same residue-field
dimension. -/
theorem finrank_residueField_kaehlerFiber_eq_localizationAtPrime
    (m : Ideal S) [m.IsMaximal] [Algebra.IsSeparable k m.ResidueField] :
    Module.finrank m.ResidueField (m.ResidueField ⊗[S] Ω[S⁄k]) =
      Module.finrank m.ResidueField
        (IsLocalRing.CotangentSpace (Localization.AtPrime m)) :=
  (finrank_residueField_kaehlerFiber_eq_cotangent (k := k) m).trans
    (localizationAtPrimeEquiv_finrank m)

/-- The intrinsic regularity criterion written using the Kähler fiber at a
maximal ideal with separable residue field. -/
theorem isRegularLocalRing_iff_finrank_residueField_kaehlerFiber_eq
    (m : Ideal S) [m.IsMaximal] [Algebra.IsSeparable k m.ResidueField]
    [IsNoetherianRing (Localization.AtPrime m)] :
    IsRegularLocalRing (Localization.AtPrime m) ↔
      Module.finrank m.ResidueField (m.ResidueField ⊗[S] Ω[S⁄k]) =
        ringKrullDim (Localization.AtPrime m) := by
  rw [IsRegularLocalRing.iff_finrank_cotangentSpace,
    ← finrank_residueField_kaehlerFiber_eq_localizationAtPrime (k := k) m]

section ClosedPoint

variable [Algebra.FiniteType k S] [IsAlgClosed k]

attribute [local instance] Ideal.Quotient.field

/-- For a maximal ideal of a finite type algebra over an algebraically closed
field, the quotient-field Kähler fiber has the same finrank as the cotangent
module of the maximal ideal. -/
@[stacks 00TR "closed-point Kähler fiber and cotangent finrank"]
theorem finrank_kaehlerFiber_eq_quotientCotangent
    (m : Ideal S) [m.IsMaximal] :
    Module.finrank (S ⧸ m) ((S ⧸ m) ⊗[S] Ω[S⁄k]) =
      Module.finrank (S ⧸ m) m.Cotangent := by
  let κm := m.ResidueField
  letI : Algebra.FiniteType k κm :=
    Algebra.FiniteType.trans (R := k) (S := S) (A := κm) inferInstance inferInstance
  letI : Module.Finite k κm :=
    finite_of_finite_type_of_isJacobsonRing k κm
  letI : Algebra.IsSeparable k κm := inferInstance
  let eFiber :
      κm ⊗[S ⧸ m] ((S ⧸ m) ⊗[S] Ω[S⁄k]) ≃ₗ[κm]
        κm ⊗[S] Ω[S⁄k] :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange S (S ⧸ m) κm κm Ω[S⁄k]
  calc
    Module.finrank (S ⧸ m) ((S ⧸ m) ⊗[S] Ω[S⁄k]) =
        Module.finrank κm (κm ⊗[S ⧸ m] ((S ⧸ m) ⊗[S] Ω[S⁄k])) :=
      Module.finrank_baseChange.symm
    _ = Module.finrank κm (κm ⊗[S] Ω[S⁄k]) := eFiber.finrank_eq
    _ = Module.finrank κm (κm ⊗[S ⧸ m] m.Cotangent) :=
      finrank_residueField_kaehlerFiber_eq_cotangent (k := k) m
    _ = Module.finrank (S ⧸ m) m.Cotangent := Module.finrank_baseChange

/-- The closed-point Kähler fiber has the same finrank as the cotangent space
of the corresponding prime localization.  This is the consumer-facing
composition of the quotient comparison and the localization comparison. -/
theorem finrank_kaehlerFiber_eq_localizationAtPrime
    (m : Ideal S) [m.IsMaximal] :
    Module.finrank (S ⧸ m) ((S ⧸ m) ⊗[S] Ω[S⁄k]) =
      Module.finrank (IsLocalRing.ResidueField (Localization.AtPrime m))
        (IsLocalRing.CotangentSpace (Localization.AtPrime m)) :=
  (finrank_kaehlerFiber_eq_quotientCotangent (k := k) m).trans
    (finrank_quotientCotangent_eq_localizationAtPrime m)

/-- The quotient-field spelling of the regularity criterion at a closed point
of a finite-type algebra over an algebraically closed field. -/
theorem isRegularLocalRing_iff_finrank_kaehlerFiber_eq
    (m : Ideal S) [m.IsMaximal] :
    IsRegularLocalRing (Localization.AtPrime m) ↔
      Module.finrank (S ⧸ m) ((S ⧸ m) ⊗[S] Ω[S⁄k]) =
        ringKrullDim (Localization.AtPrime m) := by
  letI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
  letI : IsNoetherianRing (Localization.AtPrime m) :=
    IsLocalization.isNoetherianRing m.primeCompl _ inferInstance
  rw [IsRegularLocalRing.iff_finrank_cotangentSpace,
    ← finrank_kaehlerFiber_eq_localizationAtPrime (k := k) m]

end ClosedPoint

end Ideal.Cotangent
