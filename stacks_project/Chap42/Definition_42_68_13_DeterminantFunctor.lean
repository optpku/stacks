module

public import ReasLib.Algebra.Module.FiniteLength.Determinant.Exact

open CategoryTheory
open scoped TensorProduct

universe u v

#check (Module.FiniteLengthDeterminant.exactEquiv :
  ∀ {R : Type u} [CommRing R] [IsLocalRing R]
    (S : ShortComplex (ModuleCat.{v} R))
    (h₁ : IsFiniteLength R S.X₁) (h₂ : IsFiniteLength R S.X₂)
    (h₃ : IsFiniteLength R S.X₃) (hS : S.ShortExact),
    Module.FiniteLengthDeterminant R S.X₁ h₁ ⊗[IsLocalRing.ResidueField R]
        Module.FiniteLengthDeterminant R S.X₃ h₃ ≃ₗ[IsLocalRing.ResidueField R]
      Module.FiniteLengthDeterminant R S.X₂ h₂)
