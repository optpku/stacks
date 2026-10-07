module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Pullback

/-!
# Base change of blowups

This file records the compatibility of blowups with flat base change.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {X₁ X₂ X₁' X₂' : Scheme.{u}}

/-- The pullback projection of a blowup along a flat morphism is a blowup in the inverse-image
center. -/
instance pullback_fst_isBlowup_of_flat (f : X₁ ⟶ X₂) [Flat f]
    (I₂ : X₂.IdealSheafData) (b₂ : X₂' ⟶ X₂) [IsBlowup b₂ I₂] :
    IsBlowup (pullback.fst f b₂) (I₂.comap f) := sorry

end AlgebraicGeometry

/-- Given blowups of a center and its inverse image along a flat morphism, there is a morphism
between the blowups that makes the resulting square cartesian. -/
theorem AlgebraicGeometry.IsBlowup.exists_isPullback_of_flat
    {X₁ X₂ X₁' X₂' : AlgebraicGeometry.Scheme.{u}}
    (f : X₁ ⟶ X₂) (I₂ : X₂.IdealSheafData)
    (b₁ : X₁' ⟶ X₁) (b₂ : X₂' ⟶ X₂) [AlgebraicGeometry.Flat f]
    [AlgebraicGeometry.IsBlowup b₁ (I₂.comap f)] [AlgebraicGeometry.IsBlowup b₂ I₂] :
    ∃ g' : X₁' ⟶ X₂', IsPullback g' b₁ b₂ f := sorry
