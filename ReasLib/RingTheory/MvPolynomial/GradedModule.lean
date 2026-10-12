/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import ReasLib.Algebra.Module.Rees
public import ReasLib.RingTheory.MvPolynomial.StandardGrading

@[expose] public section

noncomputable section

set_option backward.privateInPublic true

open scoped TensorProduct

universe u v w

namespace MvPolynomial

/-- The naturally graded polynomial module with coefficients in `M`; its degree-`n`
component is the tensor of homogeneous polynomials of degree `n` with `M`. -/
abbrev GradedModule (σ : Type u) (R : Type v) [CommRing R] (M : Type w)
    [AddCommGroup M] [Module R M] : Type (max u v w) :=
  DirectSum ℕ (fun n ↦ standardGrading σ R n ⊗[R] M)

namespace GradedModule

variable {σ : Type u} {R : Type v} [CommRing R]
variable {M : Type w} [AddCommGroup M] [Module R M]

/-- Insert a homogeneous polynomial tensor into its degree in the graded polynomial module. -/
def of (σ : Type u) (R : Type v) (M : Type w) [CommRing R]
    [AddCommGroup M] [Module R M] (n : ℕ) :
    (standardGrading σ R n ⊗[R] M) →ₗ[R] GradedModule σ R M :=
  DirectSum.lof R ℕ (fun d ↦ standardGrading σ R d ⊗[R] M) n

/-- The degree-`n` submodule of a graded polynomial module. -/
def grade (σ : Type u) (R : Type v) (M : Type w) [CommRing R]
    [AddCommGroup M] [Module R M] (n : ℕ) : Submodule R (GradedModule σ R M) :=
  LinearMap.range (of σ R M n)

/-- A homogeneous polynomial tensor belongs to its matching graded-module component. -/
theorem of_mem_grade (σ : Type u) (R : Type v) (M : Type w) [CommRing R]
    [AddCommGroup M] [Module R M] (n : ℕ)
    (x : standardGrading σ R n ⊗[R] M) : of σ R M n x ∈ grade σ R M n := sorry

/-- Evaluating a homogeneous polynomial at elements of `I` and applying the resulting scalar to
a module element lands in the matching stage of the `I`-adic filtration. -/
theorem eval_smul_mem_stage (I : Ideal R) (f : σ → I) (n : ℕ)
    (p : standardGrading σ R n) (x : M) :
    MvPolynomial.eval (fun i ↦ (f i : R)) p • x ∈ Ideal.PowerSubmodule.stage I M n := sorry

/-- Homogeneous polynomial evaluation acts on coefficient tensors by scalar multiplication. -/
private def evaluationTensor (I : Ideal R) (f : σ → I) (n : ℕ) :
    (standardGrading σ R n ⊗[R] M) →ₗ[R] M :=
  TensorProduct.lift ((LinearMap.lsmul R M).comp
    ((MvPolynomial.aeval (fun i ↦ (f i : R))).toLinearMap.comp
      (standardGrading σ R n).subtype))

/-- Evaluation of a homogeneous polynomial tensor lies in the corresponding ideal-power stage. -/
private theorem evaluationTensor_mem_stage (I : Ideal R) (f : σ → I) (n : ℕ)
    (tensor : standardGrading σ R n ⊗[R] M) :
    evaluationTensor I f n tensor ∈ Ideal.PowerSubmodule.stage I M n := sorry

/-- Evaluation `T_i ↦ f i` from the graded polynomial module to the Rees module. -/
def evaluation (I : Ideal R) (f : σ → I) :
    GradedModule σ R M →ₗ[R] Ideal.ReesModule I M :=
  DirectSum.toModule R ℕ _ fun n ↦ (Ideal.ReesModule.of I M n).comp
    (LinearMap.codRestrict (Ideal.PowerSubmodule.stage I M n)
      (evaluationTensor I f n) (evaluationTensor_mem_stage I f n))

/-- Evaluation on a homogeneous pure tensor is scalar evaluation followed by insertion into the
matching Rees degree. -/
theorem evaluation_of_tmul (I : Ideal R) (f : σ → I) (n : ℕ)
    (p : standardGrading σ R n) (x : M) :
    evaluation I f (of σ R M n (p ⊗ₜ[R] x)) =
      Ideal.ReesModule.of I M n
        ⟨MvPolynomial.eval (fun i ↦ (f i : R)) p • x,
          eval_smul_mem_stage I f n p x⟩ := sorry

end GradedModule
end MvPolynomial
