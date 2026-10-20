/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.EffectiveCartier.Sum
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Closed.InverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Ideal

/-!
# Pullback of sums of effective Cartier divisors

When the inverse images of two effective Cartier divisors are effective Cartier,
the inverse image of their sum is effective Cartier and is their sum over the
new ambient space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- If the inverse images of two effective Cartier divisors are effective Cartier,
then the inverse image of their sum is effective Cartier. -/
theorem pullbackDefined_effectiveCartierDivisorSum
    {S : Scheme.{u}} {X X' : AlgebraicSpace S} (f : X' ⟶ X)
    (D₁ D₂ : ClosedSubspace X)
    [IsEffectiveCartierDivisor D₁.ι] [IsEffectiveCartierDivisor D₂.ι]
    (hD₁ : IsEffectiveCartierDivisor (D₁.inverseImageSubspace f).ι)
    (hD₂ : IsEffectiveCartierDivisor (D₂.inverseImageSubspace f).ι) :
    IsEffectiveCartierDivisor
      ((effectiveCartierDivisorSum D₁ D₂).inverseImageSubspace f).ι :=
  sorry

/-- The ideal sheaf of the inverse image of a sum of effective Cartier divisors
equals the ideal sheaf of the sum of their effective Cartier inverse images. -/
theorem inverseImage_effectiveCartierDivisorSum
    {S : Scheme.{u}} {X X' : AlgebraicSpace S} (f : X' ⟶ X)
    (D₁ D₂ : ClosedSubspace X)
    [IsEffectiveCartierDivisor D₁.ι] [IsEffectiveCartierDivisor D₂.ι]
    (hD₁ : IsEffectiveCartierDivisor (D₁.inverseImageSubspace f).ι)
    (hD₂ : IsEffectiveCartierDivisor (D₂.inverseImageSubspace f).ι) :
    ((effectiveCartierDivisorSum D₁ D₂).inverseImageSubspace f).idealSheaf =
      (effectiveCartierDivisorSum
        (D₁.inverseImageSubspace f) (D₂.inverseImageSubspace f)).idealSheaf :=
  sorry

/-- If the pullbacks of two effective Cartier divisors are defined, the pullback
of their sum is defined and is isomorphic over the ambient space to their sum. -/
theorem pullback_effectiveCartierDivisorSum
    {S : Scheme.{u}} {X X' : AlgebraicSpace S} (f : X' ⟶ X)
    (D₁ D₂ : ClosedSubspace X)
    [IsEffectiveCartierDivisor D₁.ι] [IsEffectiveCartierDivisor D₂.ι]
    (hD₁ : IsEffectiveCartierDivisor (D₁.inverseImageSubspace f).ι)
    (hD₂ : IsEffectiveCartierDivisor (D₂.inverseImageSubspace f).ι) :
    IsEffectiveCartierDivisor
        ((effectiveCartierDivisorSum D₁ D₂).inverseImageSubspace f).ι ∧
      Nonempty
        (Over.mk ((effectiveCartierDivisorSum D₁ D₂).inverseImageSubspace f).ι ≅
          Over.mk (effectiveCartierDivisorSum
            (D₁.inverseImageSubspace f) (D₂.inverseImageSubspace f)).ι) := by
  refine ⟨pullbackDefined_effectiveCartierDivisorSum f D₁ D₂ hD₁ hD₂, ?_⟩
  exact (ClosedSubspace.overIso_iff_idealSheaf_eq _ _).2
    (inverseImage_effectiveCartierDivisorSum f D₁ D₂ hD₁ hD₂)

end AlgebraicGeometry.AlgebraicSpace
