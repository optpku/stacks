module

public import ReasLib.LinearAlgebra.Determinant.Projective
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.RingTheory.TensorProduct.Finite

@[expose] public section

universe u v w

namespace LinearMap

variable {A : Type u} [CommRing A]
variable {M : Type v} [AddCommGroup M] [Module A M]
  [Module.Finite A M] [Module.Projective A M]
variable {N : Type w} [AddCommGroup N] [Module A N]
  [Module.Finite A N] [Module.Projective A N]

/-- The finite-projective determinant is multiplicative on endomorphisms. -/
theorem projectiveDet_comp (f g : M →ₗ[A] M) :
    projectiveDet (f ∘ₗ g) = projectiveDet f * projectiveDet g := sorry

/-- The finite-projective determinant is cyclic on rectangular composites of equal
local rank. -/
theorem projectiveDet_comp_comm
    (h_rank : ∀ p : PrimeSpectrum A, Module.rankAtStalk M p = Module.rankAtStalk N p)
    (φ : M →ₗ[A] N) (ψ : N →ₗ[A] M) :
    projectiveDet (φ ∘ₗ ψ) = projectiveDet (ψ ∘ₗ φ) := sorry

/-- The finite-projective determinant is compatible with extension of scalars. -/
theorem projectiveDet_baseChange {A' : Type w} [CommRing A'] [Algebra A A']
    (φ : M →ₗ[A] M) :
    projectiveDet (φ.baseChange A') = algebraMap A A' (projectiveDet φ) := sorry

end LinearMap
