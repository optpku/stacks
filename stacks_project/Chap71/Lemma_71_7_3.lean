/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.EffectiveCartier.Sum.AssociatedSheaf
import StacksCheckRecall

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 71.7.3. For two effective Cartier divisors on an algebraic space over a
scheme, there is a unique isomorphism from the tensor product of their associated
sheaves to the associated sheaf of their sum preserving the canonical sections. -/
@[stacks 0842] #check
  (AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.existsUnique_associatedSheafSumIso :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      (D₁ D₂ : ClosedSubspace X)
      [IsEffectiveCartierDivisor D₁.ι] [IsEffectiveCartierDivisor D₂.ι],
      ∃! e : ClosedSubspace.associatedSheaf D₁ ⊗ ClosedSubspace.associatedSheaf D₂ ≅
        ClosedSubspace.associatedSheaf (effectiveCartierDivisorSum D₁ D₂),
        ClosedSubspace.IsAssociatedSheafSumIso D₁ D₂ e)
