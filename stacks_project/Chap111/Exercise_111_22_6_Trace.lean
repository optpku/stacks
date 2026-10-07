module

public import stacks_project.Chap49.Lemma_49_4_3_ProjectiveTrace
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.TensorProduct.Finite

@[expose] public section

universe u v w

namespace LinearMap

variable {A : Type u} [CommRing A]
variable {M : Type v} [AddCommGroup M] [Module A M]
  [Module.Finite A M] [Module.Projective A M]
variable {N : Type w} [AddCommGroup N] [Module A N]
  [Module.Finite A N] [Module.Projective A N]

/-- The finite-projective trace is cyclic on rectangular composites. -/
theorem projectiveTrace_comp_comm (φ : M →ₗ[A] N) (ψ : N →ₗ[A] M) :
    projectiveTrace (φ ∘ₗ ψ) = projectiveTrace (ψ ∘ₗ φ) := sorry

/-- The finite-projective trace is compatible with extension of scalars. -/
theorem projectiveTrace_baseChange {A' : Type w} [CommRing A'] [Algebra A A']
    (φ : M →ₗ[A] M) :
    projectiveTrace (φ.baseChange A') = algebraMap A A' (projectiveTrace φ) := sorry

end LinearMap
