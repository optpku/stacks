/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.EffectiveCartier.AssociatedSheaf
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.EffectiveCartier.Sum.Effective

/-!
# Associated sheaves of sums of effective Cartier divisors

The associated sheaf of a sum is uniquely isomorphic to the tensor product of
the associated sheaves by an isomorphism preserving their canonical sections.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace ClosedSubspace

/-- An isomorphism `associatedSheaf D₁ ⊗ associatedSheaf D₂ ≅ associatedSheaf (D₁ + D₂)`
is compatible when it sends `1_{D₁} ⊗ 1_{D₂}` to `1_D`. -/
abbrev IsAssociatedSheafSumIso {S : Scheme.{u}} {X : AlgebraicSpace S}
    (D₁ D₂ : ClosedSubspace X)
    [IsEffectiveCartierDivisor D₁.ι] [IsEffectiveCartierDivisor D₂.ι]
    (e : associatedSheaf D₁ ⊗ associatedSheaf D₂ ≅
      associatedSheaf (effectiveCartierDivisorSum D₁ D₂)) : Prop :=
  (λ_ (𝟙_ X.Modules)).inv ≫
      (canonicalSectionHom D₁ ⊗ₘ canonicalSectionHom D₂) ≫ e.hom =
    canonicalSectionHom (effectiveCartierDivisorSum D₁ D₂)

/-- For two effective Cartier divisors on an algebraic space, there is a unique
isomorphism from the tensor product of their associated sheaves to the associated
sheaf of their sum sending the tensor of their canonical sections to the
canonical section of the sum. -/
@[stacks 0842]
theorem existsUnique_associatedSheafSumIso {S : Scheme.{u}} {X : AlgebraicSpace S}
    (D₁ D₂ : ClosedSubspace X)
    [IsEffectiveCartierDivisor D₁.ι] [IsEffectiveCartierDivisor D₂.ι] :
    ∃! e : associatedSheaf D₁ ⊗ associatedSheaf D₂ ≅
      associatedSheaf (effectiveCartierDivisorSum D₁ D₂),
      IsAssociatedSheafSumIso D₁ D₂ e :=
  sorry

end ClosedSubspace

end AlgebraicGeometry.AlgebraicSpace
