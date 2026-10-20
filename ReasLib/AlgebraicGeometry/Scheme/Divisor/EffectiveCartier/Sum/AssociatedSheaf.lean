/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Sections.Tensor
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.IdealSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Sum.Effective

/-!
# Associated sheaves of sums of effective Cartier divisors

This file relates the associated sheaf of a sum of effective Cartier divisors
to the tensor product of their associated sheaves.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

/-- An isomorphism from the tensor product of two associated sheaves to the associated sheaf
of their sum is compatible when it carries the pure tensor of the canonical sections to the
canonical section of the sum. -/
abbrev IsAssociatedSheafSumIso
    (D₁ D₂ : X.IdealSheafData)
    [IsEffectiveCartierDivisor D₁.subschemeι]
    [IsEffectiveCartierDivisor D₂.subschemeι]
    (e : associatedSheaf D₁ ⊗ associatedSheaf D₂ ≅
      associatedSheaf (effectiveCartierDivisorSum D₁ D₂)) : Prop :=
  SheafOfModules.sectionsMap e.hom
      (RingedSpace.tensorSection (canonicalSection D₁) (canonicalSection D₂)) =
    canonicalSection (effectiveCartierDivisorSum D₁ D₂)

/-- For two effective Cartier divisors, there is a unique compatible isomorphism from the
tensor product of their associated sheaves to the associated sheaf of their sum. -/
theorem existsUnique_associatedSheafSumIso
    (D₁ D₂ : X.IdealSheafData)
    [IsEffectiveCartierDivisor D₁.subschemeι]
    [IsEffectiveCartierDivisor D₂.subschemeι] :
    ∃! e : associatedSheaf D₁ ⊗ associatedSheaf D₂ ≅
      associatedSheaf (effectiveCartierDivisorSum D₁ D₂),
      IsAssociatedSheafSumIso D₁ D₂ e := sorry

end AlgebraicGeometry.Scheme.IdealSheafData
