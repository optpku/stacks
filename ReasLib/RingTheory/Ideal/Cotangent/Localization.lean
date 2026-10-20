/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Ideal.CotangentBaseChange
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Ideal.Cotangent.Equiv
public import ReasLib.RingTheory.LocalRing.ResidueField.Epi

@[expose] public section

/-!
# Cotangent modules at a prime localization

The scalar towers for cotangent modules are supplied by Mathlib. Quotient and residue-field
epimorphism instances are owned by their canonical algebra constructions, so the comparison below
requires no local instance switching.

@stack 00TT
@stack 00TS
-/

open scoped TensorProduct

universe u

namespace Ideal.Cotangent

variable {R : Type u} [CommRing R]

/-- Collapsing the right tensor factor sends the tensor-extended ideal to the usual extension to
the prime localization. -/
theorem map_rid_tensorIdeal_eq_map_localizationAtPrime (p : Ideal R) [p.IsPrime] :
    Ideal.map
        (Algebra.TensorProduct.rid R (Localization.AtPrime p)
          (Localization.AtPrime p)).toRingHom
        (Ideal.map
          (Algebra.TensorProduct.includeRight.toRingHom :
            R →+* Localization.AtPrime p ⊗[R] R) p) =
      p.map (algebraMap R (Localization.AtPrime p)) := by
  rw [Ideal.map_map]
  congr 1
  ext r
  simp [Algebra.smul_def]

/-- The extension of a prime ideal to its localization is the maximal ideal of that local ring. -/
theorem map_localizationAtPrime_eq_maximalIdeal (p : Ideal R) [p.IsPrime] :
    p.map (algebraMap R (Localization.AtPrime p)) =
      IsLocalRing.maximalIdeal (Localization.AtPrime p) :=
  Localization.AtPrime.map_eq_maximalIdeal

/-- The cotangent module of a prime ideal, after passage to the residue field of its localization,
is linearly equivalent to the cotangent space of that local ring. -/
@[stacks 00TT "prime-local cotangent comparison"]
noncomputable def localizationAtPrimeEquiv (p : Ideal R) [p.IsPrime] :
    p.ResidueField ⊗[R ⧸ p] p.Cotangent ≃ₗ[p.ResidueField]
      IsLocalRing.CotangentSpace (Localization.AtPrime p) :=
  let Rp := Localization.AtPrime p
  let κp := p.ResidueField
  let eQuot : κp ⊗[R ⧸ p] p.Cotangent ≃ₗ[κp] κp ⊗[R] p.Cotangent :=
    let eQuotient : (R ⧸ p) ⊗[R] p.Cotangent ≃ₗ[R ⧸ p] p.Cotangent :=
      TensorProduct.lid' R (R ⧸ p) p.Cotangent
    let eCancel : κp ⊗[R ⧸ p] ((R ⧸ p) ⊗[R] p.Cotangent) ≃ₗ[κp]
        κp ⊗[R] p.Cotangent :=
      TensorProduct.AlgebraTensorModule.cancelBaseChange R (R ⧸ p) κp κp p.Cotangent
    (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl κp κp) eQuotient.symm).trans eCancel
  let eLocalization : κp ⊗[R] p.Cotangent ≃ₗ[κp] κp ⊗[Rp] (Rp ⊗[R] p.Cotangent) :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R Rp κp κp p.Cotangent).symm
  let tensorIdeal : Ideal (Rp ⊗[R] R) :=
    p.map (Algebra.TensorProduct.includeRight.toRingHom : R →+* Rp ⊗[R] R)
  let eTensorCotangent : κp ⊗[Rp] (Rp ⊗[R] p.Cotangent) ≃ₗ[κp]
      κp ⊗[Rp] tensorIdeal.Cotangent :=
    let e : Rp ⊗[R] p.Cotangent ≃ₗ[Rp] tensorIdeal.Cotangent :=
      Ideal.tensorCotangentEquiv R Rp p
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl κp κp) e
  let eRightUnit : Rp ⊗[R] R ≃ₐ[Rp] Rp := Algebra.TensorProduct.rid R Rp Rp
  let hTensorIdeal : tensorIdeal.map eRightUnit.toRingHom = p.map (algebraMap R Rp) :=
    map_rid_tensorIdeal_eq_map_localizationAtPrime p
  let eRightUnitCotangent : tensorIdeal.Cotangent ≃ₗ[Rp]
      (p.map (algebraMap R Rp)).Cotangent :=
    (mapAlgEquiv tensorIdeal eRightUnit).trans
      (Ideal.Cotangent.equivOfEq _ _ hTensorIdeal)
  let hMaximal : p.map (algebraMap R Rp) = IsLocalRing.maximalIdeal Rp :=
    map_localizationAtPrime_eq_maximalIdeal p
  let eMaximalCotangent : tensorIdeal.Cotangent ≃ₗ[Rp] IsLocalRing.CotangentSpace Rp :=
    eRightUnitCotangent.trans (Ideal.Cotangent.equivOfEq _ _ hMaximal)
  let eCotangent : κp ⊗[Rp] tensorIdeal.Cotangent ≃ₗ[κp]
      κp ⊗[Rp] IsLocalRing.CotangentSpace Rp :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl κp κp) eMaximalCotangent
  let eResidue : κp ⊗[Rp] IsLocalRing.CotangentSpace Rp ≃ₗ[κp]
      IsLocalRing.CotangentSpace Rp :=
    TensorProduct.lid' Rp κp (IsLocalRing.CotangentSpace Rp)
  (((eQuot.trans eLocalization).trans eTensorCotangent).trans eCotangent).trans eResidue

/-- `localizationAtPrimeEquiv` preserves finrank over the residue field of the prime
localization. -/
@[stacks 00TT "prime-local cotangent finrank comparison"]
theorem localizationAtPrimeEquiv_finrank (p : Ideal R) [p.IsPrime] :
    Module.finrank p.ResidueField (p.ResidueField ⊗[R ⧸ p] p.Cotangent) =
      Module.finrank p.ResidueField
        (IsLocalRing.CotangentSpace (Localization.AtPrime p)) :=
  (localizationAtPrimeEquiv p).finrank_eq

/-- At a maximal ideal, the quotient cotangent module and the cotangent space of the localized
local ring have the same finrank. -/
@[stacks 00TS "closed-point cotangent finrank comparison"]
theorem finrank_quotientCotangent_eq_localizationAtPrime (m : Ideal R) [m.IsMaximal] :
    Module.finrank (R ⧸ m) m.Cotangent =
      Module.finrank (IsLocalRing.ResidueField (Localization.AtPrime m))
        (IsLocalRing.CotangentSpace (Localization.AtPrime m)) := by
  -- Local instance justification (proof-local temporary data): finrank needs the field structure
  -- constructed from this theorem's explicit maximality witness; it is not globally inferable.
  letI := Ideal.Quotient.field m
  calc
    Module.finrank (R ⧸ m) m.Cotangent =
        Module.finrank m.ResidueField (m.ResidueField ⊗[R ⧸ m] m.Cotangent) :=
      Module.finrank_baseChange.symm
    _ = Module.finrank m.ResidueField
        (IsLocalRing.CotangentSpace (Localization.AtPrime m)) :=
      localizationAtPrimeEquiv_finrank m

end Ideal.Cotangent
