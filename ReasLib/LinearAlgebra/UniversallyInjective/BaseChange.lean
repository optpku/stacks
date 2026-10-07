module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.LinearAlgebra.UniversallyInjective
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
@stack 0H9I
# Reflection along universally injective algebra maps

Tensoring along an algebra map whose underlying linear map is universally injective reflects the
basic map properties recorded here.
-/

@[expose] public section

universe u v w x

namespace LinearMap

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {M : Type w} {N : Type x}
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]

/-- Lemma 10.82.14 (1): tensoring an `R`-linear map with `S` reflects injectivity when the
algebra linear map `R →ₗ[R] S` is universally injective. -/
@[stacks 0H9I]
theorem injective_of_rTensor_of_universallyInjective
    (hS : UniversallyInjective.{u, u, v, max u v w x} (Algebra.linearMap R S)) {f : M →ₗ[R] N}
    (hf : Function.Injective (f.rTensor S)) : Function.Injective f := by
  intro m n hmn
  apply (TensorProduct.lid R M).symm.injective
  apply hS.rTensor_injective M
  apply (TensorProduct.comm R S M).injective
  apply hf
  simp [hmn]

/-- Lemma 10.82.14 (2): tensoring an `R`-linear map with `S` reflects surjectivity when the
algebra linear map `R →ₗ[R] S` is universally injective. -/
@[stacks 0H9I]
theorem surjective_of_rTensor_of_universallyInjective
    (hS : UniversallyInjective.{u, u, v, max u v w x} (Algebra.linearMap R S)) {f : M →ₗ[R] N}
    (hf : Function.Surjective (f.rTensor S)) : Function.Surjective f := by
  intro n
  obtain ⟨t, ht⟩ := hf (n ⊗ₜ[R] (1 : S))
  let C := N ⧸ LinearMap.range f
  let q : N →ₗ[R] C := (LinearMap.range f).mkQ
  have hqf : q.comp f = 0 := LinearMap.range_mkQ_comp f
  have htq : q.rTensor S (n ⊗ₜ[R] (1 : S)) = 0 := by
    rw [← ht, ← LinearMap.rTensor_comp_apply, hqf, LinearMap.rTensor_zero]
    rfl
  have hqn : q n = 0 := by
    apply (TensorProduct.lid R C).symm.injective
    apply LinearMap.UniversallyInjective.rTensor_injective.{u, u, v, x, w} hS C
    simpa using congrArg (TensorProduct.comm R C S) htq
  have hn : n ∈ LinearMap.range f := by
    simpa [q, C, Submodule.mkQ_apply] using hqn
  exact hn

/-- Lemma 10.82.14 (3): tensoring an `R`-linear map with `S` reflects bijectivity when the
algebra linear map `R →ₗ[R] S` is universally injective. -/
@[stacks 0H9I]
theorem bijective_of_rTensor_of_universallyInjective
    (hS : UniversallyInjective.{u, u, v, max u v w x} (Algebra.linearMap R S)) {f : M →ₗ[R] N}
    (hf : Function.Bijective (f.rTensor S)) : Function.Bijective f :=
  ⟨injective_of_rTensor_of_universallyInjective hS hf.1,
    surjective_of_rTensor_of_universallyInjective hS hf.2⟩

end LinearMap
