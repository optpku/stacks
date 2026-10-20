module

public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.Algebra.GradedMulAction

@[expose] public section

namespace GradedModule

/-- Compatibility of an integer-graded module with a naturally graded algebra. -/
def IsCompatible {A B M : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module A M] [Module B M] (𝒜 : ℕ → Submodule A B)
    [GradedAlgebra 𝒜] (ℳ : ℤ → Submodule A M) [DirectSum.Decomposition ℳ] : Prop :=
  IsScalarTower A B M ∧
    ∀ {n : ℕ} {d : ℤ} {b : B} {m : M}, b ∈ 𝒜 n → m ∈ ℳ d → b • m ∈ ℳ ((n : ℤ) + d)

/-- The explicit degree-shift condition is equivalent to the canonical graded scalar-action interface. -/
theorem isCompatible_iff_gradedSMul {A B M : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module A M] [Module B M] (𝒜 : ℕ → Submodule A B)
    [GradedAlgebra 𝒜] (ℳ : ℤ → Submodule A M) [DirectSum.Decomposition ℳ]
    [VAdd ℕ ℤ] (hshift : ∀ n d, n +ᵥ d = (n : ℤ) + d) :
    IsCompatible 𝒜 ℳ ↔ IsScalarTower A B M ∧ SetLike.GradedSMul 𝒜 ℳ := sorry

end GradedModule
