/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.LinearAlgebra.QuotientByIdeal

/-!
# Tensor compatibility of quotient maps by ideal multiples

This leaf contains the tensor-specific extension of the ideal-quotient map
API.  The underlying quotient-map construction remains in
`ReasLib.LinearAlgebra.QuotientByIdeal`.
-/

@[expose] public section

universe u v w

namespace LinearMap

variable {R : Type u} [CommRing R]
variable {P : Type v} [AddCommGroup P] [Module R P]
variable {Q : Type w} [AddCommGroup Q] [Module R Q]

/-- The quotient map induced by a linear map commutes with the canonical identification of
tensoring by `R ⧸ J` and quotienting by `J • ⊤`. -/
@[stacks 00DV "quotient-map tensor naturality"]
theorem quotientMapByIdeal_lTensor_naturality
    (J : Ideal R) (f : P →ₗ[R] Q) :
    f.quotientMapByIdeal J ∘ₗ TensorProduct.quotTensorEquivQuotSMul P J =
      TensorProduct.quotTensorEquivQuotSMul Q J ∘ₗ f.lTensor (R ⧸ J) := by
  apply TensorProduct.ext'
  intro r x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
  simp

/-- The quotient map induced by `f` is injective exactly when tensoring `f` with `R ⧸ J` is
injective. -/
@[stacks 00DV "quotient-map tensor injectivity"]
theorem quotientMapByIdeal_injective_iff_lTensor_injective
    (J : Ideal R) (f : P →ₗ[R] Q) :
    Function.Injective (f.quotientMapByIdeal J) ↔ Function.Injective (f.lTensor (R ⧸ J)) := by
  let eP := TensorProduct.quotTensorEquivQuotSMul P J
  let eQ := TensorProduct.quotTensorEquivQuotSMul Q J
  have hnat : f.quotientMapByIdeal J ∘ₗ eP = eQ ∘ₗ f.lTensor (R ⧸ J) :=
    quotientMapByIdeal_lTensor_naturality J f
  constructor
  · intro hf x y hxy
    apply eP.injective
    apply hf
    calc
      f.quotientMapByIdeal J (eP x) = eQ (f.lTensor (R ⧸ J) x) :=
        LinearMap.congr_fun hnat x
      _ = eQ (f.lTensor (R ⧸ J) y) := congrArg eQ hxy
      _ = f.quotientMapByIdeal J (eP y) := (LinearMap.congr_fun hnat y).symm
  · intro hf x y hxy
    obtain ⟨x, rfl⟩ := eP.surjective x
    obtain ⟨y, rfl⟩ := eP.surjective y
    apply congrArg eP
    apply hf
    apply eQ.injective
    calc
      eQ (f.lTensor (R ⧸ J) x) = f.quotientMapByIdeal J (eP x) :=
        (LinearMap.congr_fun hnat x).symm
      _ = f.quotientMapByIdeal J (eP y) := hxy
      _ = eQ (f.lTensor (R ⧸ J) y) := LinearMap.congr_fun hnat y

/-- The quotient map induced by `f` is injective exactly when right-tensoring `f` with `R ⧸ J`
is injective. -/
@[stacks 00DV "quotient-map right-tensor injectivity"]
theorem quotientMapByIdeal_injective_iff_rTensor_injective
    (J : Ideal R) (f : P →ₗ[R] Q) :
    Function.Injective (f.quotientMapByIdeal J) ↔ Function.Injective (f.rTensor (R ⧸ J)) := by
  rw [quotientMapByIdeal_injective_iff_lTensor_injective,
    LinearMap.lTensor_inj_iff_rTensor_inj]

end LinearMap
