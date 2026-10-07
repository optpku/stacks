module

public import stacks_project.Chap71.Definition_71_6_6
public import stacks_project.Chap71.Lemma_71_6_12_Pullback

/-!
# Lemma 71.6.12

Pullback of effective Cartier divisors on algebraic spaces preserves sums,
whenever the pullbacks of the summands are defined.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 71.6.12 (1): if the pullbacks of two effective Cartier divisors on an
algebraic space are defined, then the pullback of their sum is defined. -/
@[stacks 0840]
theorem pullbackDefined_effectiveCartierDivisorSum
    {S : Scheme.{u}} {X X' : AlgebraicSpace S} (f : X' ⟶ X)
    (D₁ D₂ : ClosedSubspace X)
    [IsEffectiveCartierDivisor D₁.ι] [IsEffectiveCartierDivisor D₂.ι]
    (hD₁ : D₁.pullbackDefined f) (hD₂ : D₂.pullbackDefined f) :
    (effectiveCartierDivisorSum D₁ D₂).pullbackDefined f :=
  sorry

/-- Lemma 71.6.12 (2): if the pullbacks of two effective Cartier divisors are
defined, then the inverse image of their sum has the same kernel ideal as the
sum of the inverse images. -/
@[stacks 0840]
theorem inverseImage_effectiveCartierDivisorSum
    {S : Scheme.{u}} {X X' : AlgebraicSpace S} (f : X' ⟶ X)
    (D₁ D₂ : ClosedSubspace X)
    [IsEffectiveCartierDivisor D₁.ι] [IsEffectiveCartierDivisor D₂.ι]
    (hD₁ : D₁.pullbackDefined f) (hD₂ : D₂.pullbackDefined f) :
    ((effectiveCartierDivisorSum D₁ D₂).inverseImage f).idealSheaf =
      (@effectiveCartierDivisorSum S X' (D₁.inverseImage f) (D₂.inverseImage f)
        hD₁ hD₂).idealSheaf :=
  sorry

/-- The inverse image of a sum of effective Cartier divisors with defined
pullbacks is isomorphic over `X'` to the sum of the inverse images. -/
theorem inverseImage_effectiveCartierDivisorSum_overIso
    {S : Scheme.{u}} {X X' : AlgebraicSpace S} (f : X' ⟶ X)
    (D₁ D₂ : ClosedSubspace X)
    [IsEffectiveCartierDivisor D₁.ι] [IsEffectiveCartierDivisor D₂.ι]
    (hD₁ : D₁.pullbackDefined f) (hD₂ : D₂.pullbackDefined f) :
    Nonempty
      (Over.mk ((effectiveCartierDivisorSum D₁ D₂).inverseImage f).ι ≅
        Over.mk (@effectiveCartierDivisorSum S X'
          (D₁.inverseImage f) (D₂.inverseImage f) hD₁ hD₂).ι) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
