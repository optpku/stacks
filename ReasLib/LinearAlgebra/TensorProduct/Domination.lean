module

public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.Tactic.CrossRefAttribute
import Mathlib.Algebra.Module.ULift
import Mathlib.LinearAlgebra.TensorProduct.Associator

/-!
# Tensor-kernel domination

This file owns the relation between two linear maps with a common source
obtained by comparing their kernels after every tensor test.  It is independent
of the finite-presentation and filtered-colimit applications that motivated its
first use.
-/

@[expose] public section

universe u v w x

namespace LinearMap

section

variable {R : Type u} [CommSemiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]
variable {N : Type w} [AddCommMonoid N] [Module R N]
variable {M' : Type x} [AddCommMonoid M'] [Module R M']

/-- Definition 10.88.2: `g` tensor-kernel dominates `f` when every tensor test module sends
the kernel of `f ⊗ 1` into the kernel of `g ⊗ 1`. -/
@[stacks 059B "tensor-kernel domination"]
def Dominates (g : M →ₗ[R] M') (f : M →ₗ[R] N) : Prop :=
  ∀ (Q : Type (max u v w x)) [AddCommMonoid Q] [Module R Q],
    ker (f.rTensor Q) ≤ ker (g.rTensor Q)

/-- Tensor-kernel domination is precisely the family of kernel inclusions in its definition. -/
@[stacks 059B "tensor-kernel domination criterion"]
theorem dominates_iff (g : M →ₗ[R] M') (f : M →ₗ[R] N) :
    g.Dominates f ↔
      ∀ (Q : Type (max u v w x)) [AddCommMonoid Q] [Module R Q],
        ker (f.rTensor Q) ≤ ker (g.rTensor Q) := Iff.rfl

/-- Tensor-kernel domination implies inclusion of the underlying kernels. -/
@[stacks 059B "underlying kernel"]
theorem Dominates.ker_le
    {f : M →ₗ[R] N} {g : M →ₗ[R] M'} (hdom : g.Dominates f) :
    ker f ≤ ker g := by
  intro m hm
  let Q := ULift.{max v w x} R
  let e : Q ≃ₗ[R] R := ULift.moduleEquiv
  have hmQ : m ⊗ₜ[R] e.symm 1 ∈ ker (f.rTensor Q) := by
    rw [LinearMap.mem_ker, LinearMap.rTensor_tmul, LinearMap.mem_ker.mp hm,
      TensorProduct.zero_tmul]
  have hgmQ := hdom Q hmQ
  rw [LinearMap.mem_ker, LinearMap.rTensor_tmul] at hgmQ
  have hgmR := congrArg (e.lTensor M') hgmQ
  have hgm := congrArg (TensorProduct.rid R M') hgmR
  simpa using hgm

end

section

variable {R : Type u} [CommSemiring R]
variable {A A' B B' C C' D : Type v}
variable [AddCommMonoid A] [Module R A]
variable [AddCommMonoid A'] [Module R A']
variable [AddCommMonoid B] [Module R B]
variable [AddCommMonoid B'] [Module R B']
variable [AddCommMonoid C] [Module R C]
variable [AddCommMonoid C'] [Module R C']
variable [AddCommMonoid D] [Module R D]

/-- Every linear map tensor-kernel dominates itself. -/
theorem Dominates.refl (f : A →ₗ[R] B) : f.Dominates f := by
  intro Q _ _
  exact le_rfl

/-- Evaluate tensor-kernel domination at a fixed test module. -/
theorem Dominates.ker_rTensor_le
    {f : A →ₗ[R] B} {g : A →ₗ[R] C}
    (hdom : g.Dominates f)
    (Q : Type (max u v)) [AddCommMonoid Q] [Module R Q] :
    ker (f.rTensor Q) ≤ ker (g.rTensor Q) := hdom Q

/-- A map that factors through another map tensor-kernel dominates it. -/
theorem dominates_of_factorization
    {f : A →ₗ[R] B} {g : A →ₗ[R] C}
    (hfac : ∃ h : B →ₗ[R] C, g = h.comp f) :
    g.Dominates f := by
  obtain ⟨h, rfl⟩ := hfac
  intro Q _ _
  rw [LinearMap.rTensor_comp]
  exact LinearMap.ker_le_ker_comp _ _

/-- Tensor-kernel domination is stable under precomposition. -/
theorem Dominates.comp
    {f : A →ₗ[R] B} {g : A →ₗ[R] C} {h : A' →ₗ[R] A}
    (hdom : g.Dominates f) :
    (g.comp h).Dominates (f.comp h) := by
  intro Q _ _ x hx
  rw [LinearMap.mem_ker, LinearMap.rTensor_comp_apply] at hx ⊢
  exact hdom Q hx

/-- Tensor-kernel domination is transitive. -/
theorem Dominates.trans
    {f : A →ₗ[R] B} {g : A →ₗ[R] C} {h : A →ₗ[R] D}
    (hhg : h.Dominates g) (hgf : g.Dominates f) :
    h.Dominates f := by
  intro Q _ _
  exact (hgf Q).trans (hhg Q)

/-- Mutual tensor-kernel domination gives equality of kernels after each tensor test. -/
theorem Dominates.ker_rTensor_eq
    {f : A →ₗ[R] B} {g : A →ₗ[R] C}
    (hgf : g.Dominates f) (hfg : f.Dominates g)
    (Q : Type (max u v)) [AddCommMonoid Q] [Module R Q] :
    ker (f.rTensor Q) = ker (g.rTensor Q) :=
  le_antisymm (hgf Q) (hfg Q)

/-- Equality of tensor kernels for all tests implies tensor-kernel domination. -/
theorem dominates_of_ker_rTensor_eq
    {f : A →ₗ[R] B} {g : A →ₗ[R] C}
    (hker : ∀ (Q : Type (max u v)) [AddCommMonoid Q] [Module R Q],
      ker (f.rTensor Q) = ker (g.rTensor Q)) :
    g.Dominates f := by
  intro Q _ _
  exact (hker Q).le

/-- Tensor-kernel domination is invariant under simultaneous linear conjugation of the source
and both targets. -/
@[stacks 059B "conjugation"]
theorem Dominates.congr
    {f : A →ₗ[R] B} {g : A →ₗ[R] C}
    {f' : A' →ₗ[R] B'} {g' : A' →ₗ[R] C'}
    (eA : A ≃ₗ[R] A') (eB : B ≃ₗ[R] B') (eC : C ≃ₗ[R] C')
    (hf : f'.comp eA.toLinearMap = eB.toLinearMap.comp f)
    (hg : g'.comp eA.toLinearMap = eC.toLinearMap.comp g) :
    g.Dominates f ↔ g'.Dominates f' := by
  have hfQ : ∀ (Q : Type (max u v)) [AddCommMonoid Q] [Module R Q],
      (f'.rTensor Q).comp (eA.rTensor Q).toLinearMap =
        (eB.rTensor Q).toLinearMap.comp (f.rTensor Q) := by
    intro Q _ _
    simpa only [LinearEquiv.coe_rTensor, LinearMap.rTensor_comp] using
      congrArg (fun k : A →ₗ[R] B' ↦ k.rTensor Q) hf
  have hgQ : ∀ (Q : Type (max u v)) [AddCommMonoid Q] [Module R Q],
      (g'.rTensor Q).comp (eA.rTensor Q).toLinearMap =
        (eC.rTensor Q).toLinearMap.comp (g.rTensor Q) := by
    intro Q _ _
    simpa only [LinearEquiv.coe_rTensor, LinearMap.rTensor_comp] using
      congrArg (fun k : A →ₗ[R] C' ↦ k.rTensor Q) hg
  constructor
  · intro hdom Q _ _ x hx
    rw [LinearMap.mem_ker] at hx ⊢
    let x₀ := (eA.rTensor Q).symm x
    have hx₀ : (eA.rTensor Q) x₀ = x := (eA.rTensor Q).apply_symm_apply x
    have hfx₀ : f.rTensor Q x₀ = 0 := by
      apply (eB.rTensor Q).injective
      calc
        (eB.rTensor Q) (f.rTensor Q x₀) = f'.rTensor Q ((eA.rTensor Q) x₀) := by
          exact (LinearMap.congr_fun (hfQ Q) x₀).symm
        _ = f'.rTensor Q x := by rw [hx₀]
        _ = 0 := hx
        _ = (eB.rTensor Q) 0 := by simp
    have hgx₀ := LinearMap.mem_ker.mp (hdom Q (LinearMap.mem_ker.mpr hfx₀))
    calc
      g'.rTensor Q x = g'.rTensor Q ((eA.rTensor Q) x₀) := by rw [hx₀]
      _ = (eC.rTensor Q) (g.rTensor Q x₀) := LinearMap.congr_fun (hgQ Q) x₀
      _ = 0 := by rw [hgx₀]; simp
  · intro hdom Q _ _ x hx
    rw [LinearMap.mem_ker] at hx ⊢
    let x' := (eA.rTensor Q) x
    have hfx' : f'.rTensor Q x' = 0 := by
      calc
        f'.rTensor Q x' = f'.rTensor Q ((eA.rTensor Q) x) := rfl
        _ = (eB.rTensor Q) (f.rTensor Q x) := LinearMap.congr_fun (hfQ Q) x
        _ = 0 := by rw [hx]; simp
    have hgx' := LinearMap.mem_ker.mp (hdom Q (LinearMap.mem_ker.mpr hfx'))
    apply (eC.rTensor Q).injective
    calc
      (eC.rTensor Q) (g.rTensor Q x) = g'.rTensor Q ((eA.rTensor Q) x) := by
        exact (LinearMap.congr_fun (hgQ Q) x).symm
      _ = g'.rTensor Q x' := rfl
      _ = 0 := hgx'
      _ = (eC.rTensor Q) 0 := by simp

end

end LinearMap
