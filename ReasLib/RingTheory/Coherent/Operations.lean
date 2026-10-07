module

public import ReasLib.RingTheory.Coherent.Basic
public import Mathlib.RingTheory.Finiteness.Basic

@[expose] public section

/-!
# Operations on Coherent Modules

@stack 05CW

Closure properties of coherent modules under submodules, linear equivalences, kernels, images,
and cokernels.
-/

universe u v w

open Module.Finite

section

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

/-- A coherent module is finitely presented. -/
instance finitePresentation_of_coherent [Module.Coherent R M] :
    Module.FinitePresentation R M := sorry

attribute [instance 100] finitePresentation_of_coherent

/-- Lemma 10.90.3: a finite submodule of a coherent `R`-module is coherent. -/
@[stacks 05CW]
instance coherent_submodule_of_finite {P : Submodule R M}
    [Module.Coherent R M] [Module.Finite R P] :
    Module.Coherent R P := sorry

attribute [instance 100] coherent_submodule_of_finite

/-- Coherence is preserved by linear equivalences. -/
theorem coherent_of_linearEquiv {M' : Type*} [AddCommGroup M'] [Module R M']
    (e : M ≃ₗ[R] M') [hM : Module.Coherent R M] :
    Module.Coherent R M' := sorry

/-- The kernel of a map from a finite module to a coherent module is finite. -/
theorem ker_finite_of_finite_of_coherent (φ : N →ₗ[R] M) [Module.Finite R N]
    [Module.Coherent R M] :
    Module.Finite R (LinearMap.ker φ) := sorry

/-- The image of a map from a finite module to a coherent module is coherent. -/
theorem range_coherent_of_finite_of_coherent (φ : N →ₗ[R] M) [Module.Finite R N]
    [Module.Coherent R M] :
    Module.Coherent R (LinearMap.range φ) := sorry

/-- The cokernel of a map from a finite module to a coherent module is coherent. -/
theorem cokernel_coherent_of_finite_of_coherent (φ : N →ₗ[R] M) [Module.Finite R N]
    [Module.Coherent R M] :
    Module.Coherent R (M ⧸ LinearMap.range φ) := sorry

/-- The kernel of a morphism of coherent modules is coherent. -/
theorem ker_coherent_of_coherent (φ : N →ₗ[R] M) [Module.Coherent R N] [Module.Coherent R M] :
    Module.Coherent R (LinearMap.ker φ) := sorry

/-- The cokernel of a morphism of coherent modules is coherent. -/
theorem cokernel_coherent_of_coherent (φ : N →ₗ[R] M) [Module.Coherent R N]
    [Module.Coherent R M] :
    Module.Coherent R (M ⧸ LinearMap.range φ) := sorry

end
