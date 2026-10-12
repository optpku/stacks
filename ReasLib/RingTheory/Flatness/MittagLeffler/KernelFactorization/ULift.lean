/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.ULift
public import ReasLib.RingTheory.Flatness.MittagLeffler.KernelFactorization

@[expose] public section

/-!
# Universe Invariance of Finite Kernel Factorization

Finite tensor-kernel factorization is unchanged by the canonical linear equivalence between a
module and its universe lift.
-/

universe u v

namespace Module.MittagLeffler.FiniteKernelFactorization

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Finite kernel factorization is invariant under the canonical universe lift. -/
theorem iff_ulift :
    FiniteKernelFactorization R (ULift.{max u v} M) ↔ FiniteKernelFactorization R M := by
  let e : ULift.{max u v} M ≃ₗ[R] M := ULift.moduleEquiv
  constructor
  · intro h P hP f
    let f' : P →ₗ[R] ULift.{max u v} M := e.symm.toLinearMap.comp f
    obtain ⟨Q, g, hQ, hgf', hf'g⟩ := h P hP f'
    have hgf : g.Dominates f := by
      intro T _ _ x hx
      apply hgf' T
      rw [LinearMap.mem_ker] at hx ⊢
      simp [f', LinearMap.rTensor_comp_apply, hx]
    have hfg : f.Dominates g := by
      intro T _ _ x hx
      rw [LinearMap.mem_ker]
      have hx' := LinearMap.mem_ker.mp (hf'g T hx)
      have hx'' :
          (e.symm.toLinearMap.rTensor T) ((f.rTensor T) x) = 0 := by
        simpa only [f', LinearMap.rTensor_comp_apply] using hx'
      calc
        (f.rTensor T) x =
            (e.toLinearMap.rTensor T) ((e.symm.toLinearMap.rTensor T) ((f.rTensor T) x)) := by
          rw [← LinearMap.rTensor_comp_apply]
          simp
        _ = (e.toLinearMap.rTensor T) 0 := congrArg _ hx''
        _ = 0 := map_zero _
    exact ⟨Q, g, hQ, hgf, hfg⟩
  · intro h P hP f
    let f' : P →ₗ[R] M := e.toLinearMap.comp f
    obtain ⟨Q, g, hQ, hgf', hf'g⟩ := h P hP f'
    have hgf : g.Dominates f := by
      intro T _ _ x hx
      apply hgf' T
      rw [LinearMap.mem_ker] at hx ⊢
      simp [f', LinearMap.rTensor_comp_apply, hx]
    have hfg : f.Dominates g := by
      intro T _ _ x hx
      rw [LinearMap.mem_ker]
      have hx' := LinearMap.mem_ker.mp (hf'g T hx)
      have hx'' :
          (e.toLinearMap.rTensor T) ((f.rTensor T) x) = 0 := by
        simpa only [f', LinearMap.rTensor_comp_apply] using hx'
      calc
        (f.rTensor T) x =
            (e.symm.toLinearMap.rTensor T) ((e.toLinearMap.rTensor T) ((f.rTensor T) x)) := by
          rw [← LinearMap.rTensor_comp_apply]
          simp
        _ = (e.symm.toLinearMap.rTensor T) 0 := congrArg _ hx''
        _ = 0 := map_zero _
    exact ⟨Q, g, hQ, hgf, hfg⟩

end Module.MittagLeffler.FiniteKernelFactorization
