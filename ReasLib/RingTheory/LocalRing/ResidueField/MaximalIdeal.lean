/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open scoped TensorProduct

/-!
# Residue fields of maximal ideals

This leaf supplies the canonical algebra equivalence from a maximal-ideal
quotient to its residue field.  It is owned by `Ideal.ResidueField`: the
construction applies to every maximal ideal, while the local-ring form is a
convenient specialization.
-/

namespace Ideal.ResidueField

universe u v

/-- A quotient by a maximal ideal is canonically algebra-equivalent to the
residue field of that ideal. -/
noncomputable def quotientAlgEquiv
    {K : Type u} {A : Type v} [CommRing K] [CommRing A] [Algebra K A]
    (I : Ideal A) [I.IsMaximal] :
    (A ⧸ I) ≃ₐ[K] I.ResidueField :=
  AlgEquiv.ofBijective (IsScalarTower.toAlgHom K (A ⧸ I) I.ResidueField)
    (Ideal.bijective_algebraMap_quotient_residueField I)

/-- The quotient-to-residue-field equivalence sends a quotient class to its
canonical image in the residue field. -/
@[simp]
theorem quotientAlgEquiv_apply_algebraMap
    {K : Type u} {A : Type v} [CommRing K] [CommRing A] [Algebra K A]
    (I : Ideal A) [I.IsMaximal] (a : A) :
    quotientAlgEquiv (K := K) I (algebraMap A (A ⧸ I) a) =
      algebraMap A I.ResidueField a := by
  change algebraMap (A ⧸ I) I.ResidueField (Ideal.Quotient.mk I a) = _
  exact Ideal.algebraMap_quotient_residueField_mk I a

section Finrank

-- Local instance justification (instance diamond): activate the field structure on the quotient by the fixed maximal ideal only within this finrank comparison section.
attribute [local instance] Ideal.Quotient.field

/-- Extending a module first to a maximal-ideal quotient and then to its
residue field does not change its finrank.  This is the numerical companion to
`quotientAlgEquiv`. -/
theorem finrank_tensor_eq_quotient
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (I : Ideal R) [I.IsMaximal] :
    Module.finrank I.ResidueField (I.ResidueField ⊗[R] M) =
      Module.finrank (R ⧸ I) ((R ⧸ I) ⊗[R] M) := by
  let e := TensorProduct.AlgebraTensorModule.cancelBaseChange R (R ⧸ I)
    I.ResidueField I.ResidueField M
  rw [← e.finrank_eq]
  exact Module.finrank_baseChange

end Finrank

/-- For a maximal ideal, the residue-field tensor fiber of a module is
nontrivial exactly when its quotient by the ideal action is nontrivial. -/
@[stacks 00HP "maximal residue-field tensor criterion"]
theorem nontrivial_tensor_iff
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (I : Ideal R) [I.IsMaximal] :
    Nontrivial (M ⊗[R] I.ResidueField) ↔
      Nontrivial (M ⧸ I • (⊤ : Submodule R M)) := by
  let e : (M ⧸ I • (⊤ : Submodule R M)) ≃ₗ[R] M ⊗[R] I.ResidueField :=
    (TensorProduct.tensorQuotEquivQuotSMul M I).symm.trans
      (TensorProduct.congr (LinearEquiv.refl R M)
        (quotientAlgEquiv (K := R) I).toLinearEquiv)
  constructor
  · intro h
    -- Local instance justification (proof-local temporary data): install the hypothesis only while transporting nontriviality across the displayed equivalence.
    letI : Nontrivial (M ⊗[R] I.ResidueField) := h
    exact e.toEquiv.nontrivial
  · intro h
    -- Local instance justification (proof-local temporary data): install the hypothesis only while transporting nontriviality across the inverse equivalence.
    letI : Nontrivial (M ⧸ I • (⊤ : Submodule R M)) := h
    exact e.symm.toEquiv.nontrivial

end Ideal.ResidueField

namespace MaximalSpectrum

universe u

/-- The residue field associated to a maximal point of a commutative ring. -/
abbrev ResidueField {R : Type u} [CommRing R] (m : MaximalSpectrum R) :=
  m.asIdeal.ResidueField

end MaximalSpectrum

namespace IsLocalRing.ResidueField

universe u v

/-- The residue field of a local ring acts canonically on the residue field of
its maximal ideal. -/
noncomputable instance instAlgebraMaximalIdealResidueField
    (A : Type u) [CommRing A] [IsLocalRing A] :
    Algebra (IsLocalRing.ResidueField A) (IsLocalRing.maximalIdeal A).ResidueField :=
  inferInstanceAs
    (Algebra (A ⧸ IsLocalRing.maximalIdeal A) (IsLocalRing.maximalIdeal A).ResidueField)

/-- The residue field of a local ring is canonically algebra-equivalent to the
residue field of its maximal ideal. -/
noncomputable def maximalIdealAlgEquiv
    (A : Type u) [CommRing A] [IsLocalRing A] :
    IsLocalRing.ResidueField A ≃ₐ[A] (IsLocalRing.maximalIdeal A).ResidueField :=
  Ideal.ResidueField.quotientAlgEquiv (K := A) (IsLocalRing.maximalIdeal A)

/-- The quotient by the maximal ideal of a local `K`-algebra is canonically equivalent to its
ordinary residue field as a `K`-algebra. -/
noncomputable def quotientMaximalAlgEquiv
    {K : Type u} {A : Type v} [CommRing K] [CommRing A] [Algebra K A] [IsLocalRing A] :
    (A ⧸ IsLocalRing.maximalIdeal A) ≃ₐ[K] IsLocalRing.ResidueField A :=
  (Ideal.ResidueField.quotientAlgEquiv (K := K) (IsLocalRing.maximalIdeal A)).trans
    ((maximalIdealAlgEquiv A).restrictScalars K).symm

/-- The quotient-to-residue-field comparison sends a quotient class to the ordinary residue. -/
@[simp]
theorem quotientMaximalAlgEquiv_apply_algebraMap
    {K : Type u} {A : Type v} [CommRing K] [CommRing A] [Algebra K A] [IsLocalRing A]
    (a : A) :
    quotientMaximalAlgEquiv (K := K) (algebraMap A (A ⧸ IsLocalRing.maximalIdeal A) a) =
      IsLocalRing.residue A a := by
  change (maximalIdealAlgEquiv A).symm
      (maximalIdealAlgEquiv A (IsLocalRing.residue A a)) =
    IsLocalRing.residue A a
  exact (maximalIdealAlgEquiv A).symm_apply_apply _

/-- The local-ring residue-field comparison sends `residue A a` to the image
of `a` in the residue field of the maximal ideal. -/
@[simp]
theorem maximalIdealAlgEquiv_apply_residue
    (A : Type u) [CommRing A] [IsLocalRing A] (a : A) :
    maximalIdealAlgEquiv A (IsLocalRing.residue A a) =
      algebraMap A (IsLocalRing.maximalIdeal A).ResidueField a := by
  change algebraMap (A ⧸ IsLocalRing.maximalIdeal A)
      (IsLocalRing.maximalIdeal A).ResidueField
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) a) = _
  exact Ideal.algebraMap_quotient_residueField_mk (IsLocalRing.maximalIdeal A) a

/-- The inverse local-ring residue-field comparison sends the image of `a`
back to `residue A a`. -/
@[simp]
theorem maximalIdealAlgEquiv_symm_apply_algebraMap
    (A : Type u) [CommRing A] [IsLocalRing A] (a : A) :
    (maximalIdealAlgEquiv A).symm
        (algebraMap A (IsLocalRing.maximalIdeal A).ResidueField a) =
      IsLocalRing.residue A a := by
  rw [← maximalIdealAlgEquiv_apply_residue]
  exact (maximalIdealAlgEquiv A).symm_apply_apply _

/-- The inverse maximal-ideal residue-field comparisons commute with the maps
induced by local homomorphisms. -/
theorem maximalIdealAlgEquiv_symm_naturality
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (f : A →+* B) [IsLocalHom f] :
    (maximalIdealAlgEquiv B).symm.toRingHom.comp
        (Ideal.ResidueField.map (IsLocalRing.maximalIdeal A) (IsLocalRing.maximalIdeal B) f
          (IsLocalRing.maximalIdeal_comap f).symm) =
      (IsLocalRing.ResidueField.map f).comp (maximalIdealAlgEquiv A).symm.toRingHom := by
  ext a
  simp

/-- The prime-ideal residue-field map induced by the identity of a local ring
is the identity after the maximal-ideal presentation. -/
@[stacks 04GW "maximal-ideal residue-field identity", simp]
theorem map_maximalIdeal_id
    (A : Type u) [CommRing A] [IsLocalRing A] :
    Ideal.ResidueField.map (IsLocalRing.maximalIdeal A)
        (IsLocalRing.maximalIdeal A) (RingHom.id A)
        (IsLocalRing.maximalIdeal_comap (RingHom.id A)).symm =
      RingHom.id _ := by
  ext a
  simp

end IsLocalRing.ResidueField
