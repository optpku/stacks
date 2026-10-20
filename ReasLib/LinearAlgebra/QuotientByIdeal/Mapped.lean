/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.LinearAlgebra.QuotientByIdeal

/-!
# Quotient Modules Along Mapped Ideals

This leaf owns the canonical scalar actions on `M / I S M` induced by the
quotient algebra map `R / I → S / I S`.  These actions belong to quotient
base change rather than to any particular flatness or tensor argument.

@stack 0523
-/

@[expose] public section

universe u v w

namespace Ideal.Quotient.Map

section Module

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {M : Type w} [AddCommGroup M] [Module S M]

/-- The quotient module `M / I S M` is canonically an `R / I`-module through
`R / I → S / I S`. -/
@[stacks 0523 "mapped ideal quotient module"]
instance module (I : Ideal R) :
    Module (R ⧸ I) (M ⧸ (Ideal.map (algebraMap R S) I • (⊤ : Submodule S M))) :=
  Module.compHom _ (algebraMap (R ⧸ I) (S ⧸ Ideal.map (algebraMap R S) I))

/-- The quotient action of `R / I` on `M / I S M` is compatible with the ambient
`S / I S`-module action. -/
@[stacks 0523 "mapped ideal quotient scalar tower"]
instance tower_target (I : Ideal R) :
    IsScalarTower (R ⧸ I) (S ⧸ Ideal.map (algebraMap R S) I)
      (M ⧸ (Ideal.map (algebraMap R S) I • (⊤ : Submodule S M))) :=
  IsScalarTower.of_compHom _ _ _

/-- The quotient action sends the class of `m` multiplied by the class of `r` to the class of
`(algebraMap R S r) • m`. -/
@[simp, stacks 0523 "mapped ideal quotient scalar action"]
theorem mk_smul_mk (I : Ideal R) (r : R) (m : M) :
    (Ideal.Quotient.mk I r : R ⧸ I) •
        (Submodule.Quotient.mk m : M ⧸
          (Ideal.map (algebraMap R S) I • (⊤ : Submodule S M))) =
      Submodule.Quotient.mk ((algebraMap R S r) • m) := by
  change (Ideal.Quotient.mk (Ideal.map (algebraMap R S) I) (algebraMap R S r)) •
      (Submodule.Quotient.mk m : M ⧸
        (Ideal.map (algebraMap R S) I • (⊤ : Submodule S M))) = _
  rfl

end Module

section Tower

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {M : Type w} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

/-- The canonical quotient action is compatible with the original `R`-module structure on
`M / I S M`. -/
@[stacks 0523 "mapped ideal quotient source tower"]
instance tower_source (I : Ideal R) :
    IsScalarTower R (R ⧸ I)
      (M ⧸ (Ideal.map (algebraMap R S) I • (⊤ : Submodule S M))) := by
  refine IsScalarTower.of_algebraMap_smul ?_
  intro r x
  refine Submodule.Quotient.induction_on
    (Ideal.map (algebraMap R S) I • (⊤ : Submodule S M)) x ?_
  intro m
  change (Ideal.Quotient.mk I r : R ⧸ I) •
      (Submodule.Quotient.mk m : M ⧸
        (Ideal.map (algebraMap R S) I • (⊤ : Submodule S M))) = _
  rw [mk_smul_mk]
  rw [← Submodule.Quotient.mk_smul]
  rw [IsScalarTower.algebraMap_smul S r m]

/-- Restricting scalars identifies the quotient of `M` by the mapped ideal action `I S • M`
with the quotient by the source ideal action `I • M`. -/
@[stacks 0523 "mapped ideal quotient comparison"]
noncomputable def smulTopLinearEquiv (I : Ideal R) :
    (M ⧸ ((Ideal.map (algebraMap R S) I • (⊤ : Submodule S M)).restrictScalars R)) ≃ₗ[R]
      M ⧸ (I • (⊤ : Submodule R M)) :=
  Submodule.quotEquivOfEq _ _ <|
    (Ideal.smul_restrictScalars (R := R) (S := S) (M := M) I
      (⊤ : Submodule S M)).trans <|
      congrArg (I • ·) (Submodule.restrictScalars_top R (R := S) (M := M))

/-- `smulTopLinearEquiv` fixes quotient representatives. -/
@[simp, stacks 0523 "mapped ideal quotient comparison on representatives"]
theorem smulTopLinearEquiv_apply_mk (I : Ideal R) (m : M) :
    smulTopLinearEquiv (R := R) (S := S) (M := M) I (Submodule.Quotient.mk m) =
      Submodule.Quotient.mk m := by
  rfl

/-- Without manually restricting the mapped ideal submodule, the quotient by
`I S • M` is canonically the quotient by `I • M` as an `R`-module. -/
@[stacks 0523 "mapped ideal quotient comparison"]
noncomputable def smulTopQuotientEquiv (I : Ideal R) :
    (M ⧸ (Ideal.map (algebraMap R S) I • (⊤ : Submodule S M))) ≃ₗ[R]
      M ⧸ (I • (⊤ : Submodule R M)) :=
  (Submodule.Quotient.restrictScalarsEquiv R
    (Ideal.map (algebraMap R S) I • (⊤ : Submodule S M))).trans
    (smulTopLinearEquiv (R := R) (S := S) (M := M) I)

/-- The mapped-ideal quotient comparison is linear over the quotient base ring `R ⧸ I`.
This is the scalar-accurate owner for transporting flatness between the target-ideal and
source-ideal presentations of a quotient module. -/
@[stacks 0523 "mapped ideal quotient comparison over the quotient base"]
noncomputable def smulTopQuotientEquivQuotient (I : Ideal R) :
    (M ⧸ (Ideal.map (algebraMap R S) I • (⊤ : Submodule S M))) ≃ₗ[R ⧸ I]
      M ⧸ (I • (⊤ : Submodule R M)) :=
  (smulTopQuotientEquiv (R := R) (S := S) (M := M) I).extendScalarsOfSurjective
    Ideal.Quotient.mk_surjective

/-- `smulTopQuotientEquiv` fixes quotient representatives. -/
@[simp, stacks 0523 "mapped ideal quotient comparison on representatives"]
theorem smulTopQuotientEquiv_apply_mk (I : Ideal R) (m : M) :
    smulTopQuotientEquiv (R := R) (S := S) (M := M) I (Submodule.Quotient.mk m) =
      Submodule.Quotient.mk m := by
  rfl

/-- The quotient-base-linear mapped-ideal comparison fixes quotient representatives. -/
@[simp, stacks 0523 "mapped ideal quotient comparison over the quotient base"]
theorem smulTopQuotientEquivQuotient_apply_mk (I : Ideal R) (m : M) :
    smulTopQuotientEquivQuotient (R := R) (S := S) (M := M) I
        (Submodule.Quotient.mk m) =
      Submodule.Quotient.mk m := by
  exact smulTopQuotientEquiv_apply_mk (R := R) (S := S) (M := M) I m

/-- The inverse `smulTopQuotientEquiv` also fixes quotient representatives. -/
@[simp, stacks 0523 "mapped ideal quotient inverse on representatives"]
theorem smulTopQuotientEquiv_symm_apply_mk (I : Ideal R) (m : M) :
    (smulTopQuotientEquiv (R := R) (S := S) (M := M) I).symm
      (Submodule.Quotient.mk m) = Submodule.Quotient.mk m := by
  apply (smulTopQuotientEquiv (R := R) (S := S) (M := M) I).injective
  simp

/-- `smulTopQuotientEquiv` intertwines the quotient map induced by multiplication by `s : S`
with multiplication by the class of `s` on quotient representatives. -/
@[stacks 0523 "mapped ideal quotient multiplication"]
theorem smulTopQuotientEquiv_lsmul_mk (I : Ideal R) (s : S) (m : M) :
    (((LinearMap.lsmul S M s).restrictScalars R).quotientMapByIdeal I)
        (smulTopQuotientEquiv (R := R) (S := S) (M := M) I
          (Submodule.Quotient.mk m)) =
      smulTopQuotientEquiv (R := R) (S := S) (M := M) I
        ((Ideal.Quotient.mk (Ideal.map (algebraMap R S) I) s) •
          (Submodule.Quotient.mk m : M ⧸
            (Ideal.map (algebraMap R S) I • (⊤ : Submodule S M)))) := by
  rw [smulTopQuotientEquiv_apply_mk]
  change Submodule.Quotient.mk (s • m) = _
  rw [Module.Quotient.mk_smul_mk, smulTopQuotientEquiv_apply_mk]

end Tower

section Containment

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {M : Type w} [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]

/-- If a source ideal maps into a target ideal, the target module quotient carries the
expected scalar tower from the source ring through its quotient.  This is the containment form
of `tower_source`; it applies when the target denominator is only propositionally, rather than
definitionally, the extension of the source ideal. -/
@[stacks 0523 "quotient target scalar tower under ideal containment"]
theorem tower_source_of_le_comap (I : Ideal R) (J : Ideal S)
    (hIJ : I ≤ Ideal.comap (algebraMap R S) J) :
    letI : Algebra (R ⧸ I) (S ⧸ J) :=
      Ideal.Quotient.algebraQuotientOfLEComap hIJ
    letI : Module (R ⧸ I) (M ⧸ (J • (⊤ : Submodule S M))) :=
      Module.compHom _ (algebraMap (R ⧸ I) (S ⧸ J))
    IsScalarTower R (R ⧸ I) (M ⧸ (J • (⊤ : Submodule S M))) := by
  letI : Algebra (R ⧸ I) (S ⧸ J) :=
    Ideal.Quotient.algebraQuotientOfLEComap hIJ
  let quotientModule : Module (S ⧸ J) (M ⧸ (J • (⊤ : Submodule S M))) :=
    inferInstance
  letI : Module (S ⧸ J) (M ⧸ (J • (⊤ : Submodule S M))) := quotientModule
  letI : SMul (S ⧸ J) (M ⧸ (J • (⊤ : Submodule S M))) := quotientModule.toSMul
  let sourceModule : Module (R ⧸ I) (M ⧸ (J • (⊤ : Submodule S M))) :=
    Module.compHom _ (algebraMap (R ⧸ I) (S ⧸ J))
  letI : Module (R ⧸ I) (M ⧸ (J • (⊤ : Submodule S M))) := sourceModule
  refine IsScalarTower.of_algebraMap_smul ?_
  intro r x
  refine Submodule.Quotient.induction_on (J • (⊤ : Submodule S M)) x ?_
  intro m
  change (algebraMap (R ⧸ I) (S ⧸ J) (algebraMap R (R ⧸ I) r)) •
      (Submodule.Quotient.mk m : M ⧸ (J • (⊤ : Submodule S M))) =
    r • (Submodule.Quotient.mk m : M ⧸ (J • (⊤ : Submodule S M)))
  have hmap : algebraMap (R ⧸ I) (S ⧸ J) (algebraMap R (R ⧸ I) r) =
      Ideal.Quotient.mk J (algebraMap R S r) := rfl
  rw [hmap, Module.Quotient.mk_smul_mk]
  rw [← Submodule.Quotient.mk_smul (J • (⊤ : Submodule S M)) (r := r) (x := m)]
  rw [IsScalarTower.algebraMap_smul S r m]

end Containment

section Algebra

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S]
variable [Algebra R S]

/-- The extension of a base ideal acts on its ambient algebra as the corresponding ideal
submodule.  This is the coercion-normalized form needed for the ring-quotient comparison. -/
theorem mappedIdeal_smulTop_eq (I : Ideal R) :
    Ideal.map (algebraMap R S) I • (⊤ : Submodule S S) =
      Ideal.map (algebraMap R S) I := by
  rw [Ideal.smul_eq_mul, Ideal.mul_top]

/-- The source ideal quotient of an algebra, viewed as an `R`-module, is canonically the quotient
by the mapped ideal in the algebra.  This is the ring-quotient view of
`smulTopQuotientEquiv`; the latter remains the more general module owner. -/
@[stacks 0523 "mapped ideal ring quotient comparison"]
noncomputable def idealQuotientEquiv (I : Ideal R) :
    (S ⧸ (I • (⊤ : Submodule R S))) ≃ₗ[R]
      S ⧸ Ideal.map (algebraMap R S) I :=
  (smulTopQuotientEquiv (R := R) (S := S) (M := S) I).symm.trans
    ((Submodule.quotEquivOfEq
      (Ideal.map (algebraMap R S) I • (⊤ : Submodule S S))
      (Ideal.map (algebraMap R S) I)
      (mappedIdeal_smulTop_eq (R := R) (S := S) I)).restrictScalars R)

/-- `idealQuotientEquiv` sends a source quotient representative to the same class in the mapped
ideal quotient. -/
@[simp, stacks 0523 "mapped ideal ring quotient representative"]
theorem idealQuotientEquiv_apply_mk (I : Ideal R) (s : S) :
    idealQuotientEquiv (R := R) (S := S) I (Submodule.Quotient.mk s) =
      Ideal.Quotient.mk (Ideal.map (algebraMap R S) I) s := by
  change (Submodule.quotEquivOfEq _ _
      (mappedIdeal_smulTop_eq (R := R) (S := S) I))
      ((smulTopQuotientEquiv (R := R) (S := S) (M := S) I).symm
        (Submodule.Quotient.mk s)) = _
  rw [smulTopQuotientEquiv_symm_apply_mk]
  rfl

/-- The inverse of `idealQuotientEquiv` sends a mapped ideal quotient representative back to the
source quotient representative. -/
@[simp, stacks 0523 "mapped ideal ring quotient inverse representative"]
theorem idealQuotientEquiv_symm_apply_mk (I : Ideal R) (s : S) :
    (idealQuotientEquiv (R := R) (S := S) I).symm
        (Ideal.Quotient.mk (Ideal.map (algebraMap R S) I) s) =
      Submodule.Quotient.mk s := by
  apply (idealQuotientEquiv (R := R) (S := S) I).injective
  simp

end Algebra

end Ideal.Quotient.Map
