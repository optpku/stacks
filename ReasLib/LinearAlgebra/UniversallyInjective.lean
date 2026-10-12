/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.Algebra.Module.ULift

/-!
# Universally injective linear maps

This file owns the tensor-stable injectivity condition for linear maps.  It is independent of the
short-complex applications that use it to define universal exactness.
-/

@[expose] public section

universe u v w z t

namespace LinearMap

variable {R : Type u} [CommRing R]
variable {M : Type v} {N : Type w}
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- An `R`-linear map is universally injective when tensoring it with every `R`-module preserves
injectivity. -/
@[stacks 058I]
def UniversallyInjective (f : M →ₗ[R] N) : Prop :=
  ∀ (Q : Type z) (_ : AddCommGroup Q) (_ : Module R Q),
    Function.Injective (f.rTensor Q)

/-- A linear map with a linear retraction is universally injective. -/
theorem universallyInjective_of_retraction (f : M →ₗ[R] N) (r : N →ₗ[R] M)
    (h : r.comp f = LinearMap.id) : UniversallyInjective.{u, v, w, z} f := sorry

/-- The identity map of an `R`-module is universally injective. -/
@[stacks 058I "identity map"]
theorem universallyInjective_id :
    UniversallyInjective (LinearMap.id : M →ₗ[R] M) := by
  intro Q _ _
  rw [LinearMap.rTensor_id]
  exact Function.injective_id

/-- Evaluate universal injectivity at a chosen tensor test module. -/
@[stacks 058I "tensor-test evaluation"]
theorem UniversallyInjective.rTensor_injective
    {f : M →ₗ[R] N}
    (hf : UniversallyInjective.{u, v, w, max u v w z t} f)
    (Q : Type z) [AddCommGroup Q] [Module R Q] :
    Function.Injective (f.rTensor Q) := by
  let Q' := ULift.{max u v w t} Q
  let e : Q' ≃ₗ[R] Q := ULift.moduleEquiv
  have hQ' : Function.Injective (f.rTensor Q') := hf Q' _ _
  intro x y hxy
  apply (e.symm.lTensor M).injective
  apply hQ'
  calc
    f.rTensor Q' ((e.symm.lTensor M) x) =
        TensorProduct.map f e.symm.toLinearMap x := by
      change ((f.rTensor Q').comp (e.symm.toLinearMap.lTensor M)) x = _
      rw [LinearMap.rTensor_comp_lTensor]
    _ = (e.symm.lTensor N) (f.rTensor Q x) := by
      change _ = ((e.symm.toLinearMap.lTensor N).comp (f.rTensor Q)) x
      rw [LinearMap.lTensor_comp_rTensor]
    _ = (e.symm.lTensor N) (f.rTensor Q y) := congrArg _ hxy
    _ = TensorProduct.map f e.symm.toLinearMap y := by
      change ((e.symm.toLinearMap.lTensor N).comp (f.rTensor Q)) y = _
      rw [LinearMap.lTensor_comp_rTensor]
    _ = f.rTensor Q' ((e.symm.lTensor M) y) := by
      change _ = ((f.rTensor Q').comp (e.symm.toLinearMap.lTensor M)) y
      rw [LinearMap.rTensor_comp_lTensor]

/-- A universally injective linear map is injective. -/
@[stacks 058I "underlying injectivity"]
theorem UniversallyInjective.injective
    {f : M →ₗ[R] N}
    (hf : UniversallyInjective.{u, v, w, max u v w z} f) :
    Function.Injective f := by
  intro x y hxy
  have hxy' : x ⊗ₜ[R] (1 : R) = y ⊗ₜ[R] (1 : R) := by
    apply hf.rTensor_injective R
    simpa using congrArg (fun z : N ↦ z ⊗ₜ[R] (1 : R)) hxy
  simpa using congrArg (TensorProduct.rid R M) hxy'

variable {M₂ : Type v} {N₂ : Type w}
variable [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]

/-- Products of universally injective linear maps are universally injective. -/
@[stacks 058N "product of universally injective maps"]
theorem UniversallyInjective.prodMap {f : M →ₗ[R] N} {g : M₂ →ₗ[R] N₂}
    (hf : UniversallyInjective.{u, v, w, z} f)
    (hg : UniversallyInjective.{u, v, w, z} g) :
    UniversallyInjective.{u, v, w, z} (f.prodMap g) := by
  intro Q _ _
  have hcomm :
      ((f.rTensor Q).prodMap (g.rTensor Q)).comp
          (TensorProduct.prodLeft R R M M₂ Q).toLinearMap =
        (TensorProduct.prodLeft R R N N₂ Q).toLinearMap.comp
          ((f.prodMap g).rTensor Q) := by
    apply TensorProduct.ext
    rfl
  intro x y hxy
  apply (TensorProduct.prodLeft R R M M₂ Q).injective
  apply (hf Q _ _).prodMap (hg Q _ _)
  change (((f.rTensor Q).prodMap (g.rTensor Q)).comp
      (TensorProduct.prodLeft R R M M₂ Q).toLinearMap) x =
    (((f.rTensor Q).prodMap (g.rTensor Q)).comp
      (TensorProduct.prodLeft R R M M₂ Q).toLinearMap) y
  rw [hcomm]
  exact congrArg (TensorProduct.prodLeft R R N N₂ Q) hxy

end LinearMap

namespace RingHom

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- An algebra map with a ring-homomorphic retraction is universally injective as a linear map. -/
theorem universallyInjective_algebraMap_of_retraction (rho : S →+* R)
    (h_rho : rho.comp (algebraMap R S) = RingHom.id R) :
    LinearMap.UniversallyInjective.{u, u, v, z} (Algebra.linearMap R S) := sorry

end RingHom
