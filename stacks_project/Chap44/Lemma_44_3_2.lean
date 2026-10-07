module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Relative.SumRank
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

/- Lemma 44.3.2: on a smooth relative curve, the canonical sum of closed subschemes
finite locally free of ranks `d₁` and `d₂` is finite locally free of rank `d₁ + d₂`. -/
@[stacks 0B9E] #check
  (AlgebraicGeometry.Scheme.IdealSheafData.isFiniteLocallyFreeOfRank_sum :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [SmoothOfRelativeDimension 1 f]
      (D₁ D₂ : X.IdealSheafData) (d₁ d₂ : ℕ),
      IsFiniteLocallyFreeOfRank (D₁.subschemeι ≫ f) d₁ →
        IsFiniteLocallyFreeOfRank (D₂.subschemeι ≫ f) d₂ →
          IsFiniteLocallyFreeOfRank
            ((effectiveCartierDivisorSum D₁ D₂).subschemeι ≫ f) (d₁ + d₂))

end AlgebraicGeometry.Scheme.IdealSheafData
