module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Sum.AssociatedSheaf
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory

universe u

/- Lemma 31.14.4: for effective Cartier divisors `D₁` and `D₂` on a scheme, there is a unique
isomorphism from the tensor product of their associated sheaves to the associated sheaf of their
sum which carries the pure tensor of their canonical sections to the canonical section of the
sum. -/
@[stacks 02OP] #check
  (AlgebraicGeometry.Scheme.IdealSheafData.existsUnique_associatedSheafSumIso :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} (D₁ D₂ : X.IdealSheafData)
      [AlgebraicGeometry.IsEffectiveCartierDivisor D₁.subschemeι]
      [AlgebraicGeometry.IsEffectiveCartierDivisor D₂.subschemeι],
      ∃! e :
        AlgebraicGeometry.Scheme.IdealSheafData.associatedSheaf D₁ ⊗
            AlgebraicGeometry.Scheme.IdealSheafData.associatedSheaf D₂ ≅
          AlgebraicGeometry.Scheme.IdealSheafData.associatedSheaf
            (AlgebraicGeometry.effectiveCartierDivisorSum D₁ D₂),
        AlgebraicGeometry.Scheme.IdealSheafData.IsAssociatedSheafSumIso D₁ D₂ e)
