/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.LinearAlgebra.QuotientByIdeal
public import ReasLib.LinearAlgebra.QuotientByIdeal.Scalar

/-!
# Quotient maps over quotient rings

This leaf upgrades the `R`-linear quotient map by an ideal to a linear map
over the quotient ring when the ideal is two-sided.
-/

@[expose] public section

universe u v w

noncomputable section

open scoped TensorProduct

namespace Ideal.Quotient

variable {R : Type u} [CommRing R]

/-- The canonical `R ⧸ I`-linear identification of scalar extension with quotienting a module by
the multiples of `I`. -/
@[stacks 00DV "tensor description of a module modulo a base ideal"]
def tensorModuleEquiv (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] :
    ((R ⧸ I) ⊗[R] M) ≃ₗ[R ⧸ I] M ⧸ (I • (⊤ : Submodule R M)) :=
  (TensorProduct.quotTensorEquivQuotSMul M I).extendScalarsOfSurjective
    Ideal.Quotient.mk_surjective

/-- The tensor-module identification sends a pure tensor with coefficient one to the quotient
class of its module factor. -/
@[simp]
theorem tensorModuleEquiv_one_tmul (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] (x : M) :
    tensorModuleEquiv I M (1 ⊗ₜ[R] x) = Submodule.Quotient.mk x := by
  change TensorProduct.quotTensorEquivQuotSMul M I (1 ⊗ₜ[R] x) =
    Submodule.Quotient.mk x
  exact TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul I x

/- The scalar-linear form is the preferred rewrite for downstream basis and tensor arguments. -/
/-- The quotient-ring/tensor equivalence sends a pure tensor to scalar multiplication of the
quotient class. -/
@[stacks 00DV "tensor quotient pure-tensor scalar formula"]
theorem tensorModuleEquiv_tmul (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] (r : R ⧸ I) (x : M) :
    tensorModuleEquiv I M (r ⊗ₜ[R] x) = r • Submodule.Quotient.mk x := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
  change TensorProduct.quotTensorEquivQuotSMul M I
      (Ideal.Quotient.mk I r ⊗ₜ[R] x) =
    Ideal.Quotient.mk I r • Submodule.Quotient.mk x
  simpa using TensorProduct.quotTensorEquivQuotSMul_mk_tmul (M := M) I r x

/- The inverse formula avoids forcing consumers to unfold the scalar extension construction. -/
/-- The inverse quotient-ring/tensor equivalence sends a quotient class to the pure tensor with
coefficient one. -/
@[stacks 00DV "inverse tensor quotient pure-tensor formula"]
theorem tensorModuleEquiv_symm_mk (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] (x : M) :
    (tensorModuleEquiv I M).symm (Submodule.Quotient.mk x) = 1 ⊗ₜ[R] x := by
  change (TensorProduct.quotTensorEquivQuotSMul M I).symm
      (Submodule.Quotient.mk x) = 1 ⊗ₜ[R] x
  exact TensorProduct.quotTensorEquivQuotSMul_symm_mk I x

end Ideal.Quotient

namespace LinearMap.IdealQuotient

section Map

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {M' : Type w} [AddCommGroup M'] [Module R M']

/-- The canonical `R ⧸ I`-linear map induced by an `R`-linear map on quotients by the multiples
of `I`.  The longer `quotientMapByIdeal_over_quotient` name remains as a compatibility bridge. -/
@[stacks 00DV "linear maps modulo a base ideal"]
abbrev map (f : M →ₗ[R] M') (I : Ideal R) [I.IsTwoSided] :
    M ⧸ (I • (⊤ : Submodule R M)) →ₗ[R ⧸ I]
      M' ⧸ (I • (⊤ : Submodule R M')) :=
  LinearMap.extendScalarsOfQuotient (R := R) (I := I) (f.quotientMapByIdeal I)

/-- The quotient-ring-linear map sends a quotient representative to the class of its image. -/
@[simp]
theorem map_mk (f : M →ₗ[R] M') (I : Ideal R) [I.IsTwoSided] (x : M) :
    map f I (Submodule.Quotient.mk x) = Submodule.Quotient.mk (f x) :=
  f.quotientMapByIdeal_apply_mk I x

end Map

end LinearMap.IdealQuotient

namespace LinearMap

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {M' : Type w} [AddCommGroup M'] [Module R M']

/-- Historical long name for `LinearMap.IdealQuotient.map`; retained for source compatibility. -/
@[stacks 00DV "compatibility alias for quotient-ring linear maps"]
abbrev quotientMapByIdeal_over_quotient
    (f : M →ₗ[R] M') (I : Ideal R) [I.IsTwoSided] :
    M ⧸ (I • (⊤ : Submodule R M)) →ₗ[R ⧸ I]
      M' ⧸ (I • (⊤ : Submodule R M')) :=
  LinearMap.IdealQuotient.map f I

/-- Representative formula for the historical quotient-ring map name. -/
@[simp]
theorem quotientMapByIdeal_over_quotient_apply_mk
    (f : M →ₗ[R] M') (I : Ideal R) [I.IsTwoSided] (x : M) :
    f.quotientMapByIdeal_over_quotient I (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (f x) :=
  LinearMap.IdealQuotient.map_mk f I x

end LinearMap

namespace LinearMap.IdealQuotient

section Descend

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {M' : Type w} [AddCommGroup M'] [Module R M']

/-- Descend an `R`-linear map with values modulo `I` to an `R ⧸ I`-linear map on the
source modulo `I`. -/
@[stacks 00DV "linear descent between modules modulo a base ideal"]
def descend (I : Ideal R)
    (f : M →ₗ[R] M' ⧸ (I • (⊤ : Submodule R M')))
    (hf : I • (⊤ : Submodule R M) ≤ LinearMap.ker f) :
    M ⧸ (I • (⊤ : Submodule R M)) →ₗ[R ⧸ I]
      M' ⧸ (I • (⊤ : Submodule R M')) :=
  ((I • (⊤ : Submodule R M)).liftQ f hf).extendScalarsOfSurjective
    Ideal.Quotient.mk_surjective

/-- Quotient-linear descent sends the class of a representative to its prescribed value. -/
@[simp]
theorem descend_mk (I : Ideal R)
    (f : M →ₗ[R] M' ⧸ (I • (⊤ : Submodule R M')))
    (hf : I • (⊤ : Submodule R M) ≤ LinearMap.ker f) (x : M) :
    descend I f hf (Submodule.Quotient.mk x) = f x := rfl

end Descend

end LinearMap.IdealQuotient
