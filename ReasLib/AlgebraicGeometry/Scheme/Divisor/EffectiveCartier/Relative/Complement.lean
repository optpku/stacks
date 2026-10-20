module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Relative.Difference
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Relative.SmoothCurve
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Relative.SumRank
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Sum.Factorization

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- On a smooth relative curve, an inclusion of finite locally free closed subschemes
admits a finite locally free effective-Cartier complement whose rank is the difference of
the two ranks. -/
theorem exists_complement_of_le
    {X S : Scheme.{u}} (f : X ⟶ S) [SmoothOfRelativeDimension 1 f]
    (D₁ D₂ : X.IdealSheafData) (d₁ d₂ : ℕ)
    (hD₁ : IsFiniteLocallyFreeOfRank (D₁.subschemeι ≫ f) d₁)
    (hD₂ : IsFiniteLocallyFreeOfRank (D₂.subschemeι ≫ f) d₂)
    (h : D₂ ≤ D₁) :
    ∃ D : X.IdealSheafData,
      IsFiniteLocallyFreeOfRank (D.subschemeι ≫ f) (d₂ - d₁) ∧
        D₂ = effectiveCartierDivisorSum D₁ D := sorry

end AlgebraicGeometry.Scheme.IdealSheafData
