/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Ideal.AssociatedGraded.Module

/-!
# Tensor maps to associated graded pieces

@stack 0AS8

This leaf owns the canonical map from the tensor product with an ideal-power
quotient to the corresponding associated graded module piece.
-/

@[expose] public section

open scoped Pointwise TensorProduct

universe u v

namespace Ideal.AssociatedGraded

variable {R : Type u} [CommRing R]

/-- The unrestricted tensor-to-scalar-multiplication map has image in `I ^ n M`. -/
theorem tensorToStage_mem
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] (n : ℕ)
    (x : M ⊗[R] ↥(I ^ n : Ideal R)) :
    ((TensorProduct.rid R M).toLinearMap.comp
      (TensorProduct.map (LinearMap.id : M →ₗ[R] M) ((I ^ n : Ideal R).subtype))) x ∈
        stage I M n := sorry

/-- The tensor-to-scalar-multiplication map with codomain restricted to `I ^ n M`. -/
noncomputable def tensorToStage
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] (n : ℕ) :
    M ⊗[R] ↥(I ^ n : Ideal R) →ₗ[R] ↥(stage I M n) :=
  LinearMap.codRestrict (stage I M n)
    ((TensorProduct.rid R M).toLinearMap.comp
      (TensorProduct.map (LinearMap.id : M →ₗ[R] M) ((I ^ n : Ideal R).subtype)))
    (tensorToStage_mem I M n)

/-- Tensoring the denominator `I(I ^ n)` maps into the internal denominator `I(I ^ n M)`. -/
theorem tensorToStage_range_le
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] (n : ℕ) :
    LinearMap.range
        (TensorProduct.map (LinearMap.id : M →ₗ[R] M)
          ((I • (⊤ : Submodule R ↥(I ^ n : Ideal R))).subtype)) ≤
      Submodule.comap (tensorToStage I M n) (internalDenominator I M n) := sorry

/-- The canonical map
`M ⊗[R] (I ^ n / I ^ (n + 1)) → I ^ n M / I ^ (n + 1) M`. -/
@[stacks 0AS8 "canonical tensor map to an associated graded piece"]
noncomputable def tensorToPiece
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] (n : ℕ) :
    M ⊗[R] ((I ^ n : Ideal R) ⧸ (I • (⊤ : Submodule R ↥(I ^ n : Ideal R)))) →ₗ[R]
      piece I M n :=
  (internalPieceEquiv I M n).toLinearMap.comp
    (((LinearMap.range
        (TensorProduct.map (LinearMap.id : M →ₗ[R] M)
          ((I • (⊤ : Submodule R ↥(I ^ n : Ideal R))).subtype))).mapQ
      (internalDenominator I M n) (tensorToStage I M n)
      (tensorToStage_range_le I M n)).comp
      (TensorProduct.tensorQuotientEquiv M
        (I • (⊤ : Submodule R ↥(I ^ n : Ideal R)))).toLinearMap)

/-- On a pure tensor, `tensorToPiece` sends `m ⊗ a` to the class of `a • m`. -/
@[simp]
theorem tensorToPiece_tmul_mk
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]
    (n : ℕ) (m : M) (a : ↥(I ^ n : Ideal R)) :
    tensorToPiece I M n (m ⊗ₜ[R] Submodule.Quotient.mk a) =
      Submodule.Quotient.mk ⟨a.1 • m, by
        have haStage : a.1 ∈ stage I R n := by
          change a.1 ∈ (I ^ n) • (⊤ : Submodule R R)
          simp [a.2]
        simpa using
          (smul_mem_stage I
            (⟨a.1, haStage⟩ : stage I R n)
            (⟨m, mem_stage_zero I M m⟩ : stage I M 0))⟩ := sorry

/-- The canonical map from the tensor product with an ideal-power quotient to the corresponding
associated graded module piece is surjective. -/
theorem tensorToPiece_surjective
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] (n : ℕ) :
    Function.Surjective (tensorToPiece I M n) := sorry

/-- If the module is flat, the canonical map from the tensor product with an ideal-power
quotient to the corresponding associated graded module piece is bijective. -/
theorem tensorToPiece_bijective_of_flat
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] [Module.Flat R M]
    (n : ℕ) : Function.Bijective (tensorToPiece I M n) := sorry

end Ideal.AssociatedGraded
