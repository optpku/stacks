/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.LinearAlgebra.UniversallyInjective

/-!
# Operations on universally injective linear maps

@stack 05CH
@stack 05CI
@stack 05CJ

The tensor-stable injectivity predicate is defined in the parent module; this file contains its
basic tensor, composition, and cancellation operations.
-/

@[expose] public section

open scoped TensorProduct

universe u v w x y z

namespace LinearMap

variable {R : Type u} [CommRing R]
variable {M : Type v} {M' : Type w} {N : Type x}
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup M'] [Module R M']
variable [AddCommGroup N] [Module R N]

/-- Universal injectivity is preserved when the underlying linear map is replaced by an equal
map.  Keeping this transport as an atomic theorem prevents clients from unfolding every tensor
test while rewriting the predicate. -/
theorem UniversallyInjective.congr {f g : M →ₗ[R] M'}
    (hf : UniversallyInjective.{u, v, w, y} f) (hfg : f = g) :
    UniversallyInjective.{u, v, w, y} g := by
  subst g
  exact hf

/-- Lemma 10.82.8: right tensoring a universally injective linear map by any module yields a
universally injective linear map. -/
@[stacks 05CH]
theorem universallyInjective_rTensor
    {f : M →ₗ[R] M'} (hf : UniversallyInjective.{u, v, w, max x y} f) :
    UniversallyInjective.{u, max v x, max w x, y} (f.rTensor N) := by
  intro Q _ _
  intro a b hab
  apply (TensorProduct.assoc R M N Q).injective
  apply hf (N ⊗[R] Q) _ _
  have hab' := congrArg (TensorProduct.assoc R M' N Q) hab
  simpa [LinearMap.rTensor_tensor, LinearMap.comp_apply] using hab'

/-- Lemma 10.82.9: the composite of universally injective linear maps is universally injective. -/
@[stacks 05CI]
theorem universallyInjective_comp
    {P : Type y} [AddCommGroup P] [Module R P]
    {f : M →ₗ[R] M'} {g : M' →ₗ[R] P}
    (hg : UniversallyInjective.{u, w, y, z} g)
    (hf : UniversallyInjective.{u, v, w, z} f) :
    UniversallyInjective.{u, v, y, z} (g.comp f) := by
  intro Q _ _
  rw [LinearMap.rTensor_comp]
  exact (hg Q _ _).comp (hf Q _ _)

/-- Lemma 10.82.10: universal injectivity of a composite implies universal injectivity of its
left factor. -/
@[stacks 05CJ]
theorem universallyInjective_of_comp
    {M'' : Type y} [AddCommGroup M''] [Module R M'']
    {f : M →ₗ[R] M'} {g : M' →ₗ[R] M''}
    (hgf : UniversallyInjective.{u, v, y, z} (g.comp f)) :
    UniversallyInjective.{u, v, w, z} f := by
  intro Q _ _
  intro x y hxy
  apply hgf Q _ _
  rw [LinearMap.rTensor_comp]
  exact congrArg (g.rTensor Q) hxy

end LinearMap

namespace LinearEquiv

variable {R : Type u} [CommRing R]
variable {M : Type v} {M' : Type w}
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup M'] [Module R M']

/-- A linear equivalence is universally injective as a linear map. -/
theorem universallyInjective (e : M ≃ₗ[R] M') :
    LinearMap.UniversallyInjective.{u, v, w, z} e.toLinearMap := by
  intro Q _ _
  exact (e.rTensor Q).injective

end LinearEquiv
