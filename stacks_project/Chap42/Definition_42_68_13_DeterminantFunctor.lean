/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

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
