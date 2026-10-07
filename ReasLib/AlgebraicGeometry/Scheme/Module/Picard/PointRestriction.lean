module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.IdealSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Pullback

/-!
# Nonextension of positive multiples of a closed-point Picard class
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- The Picard class of the invertible sheaf `𝒪(y)` associated to a closed
effective Cartier point `y`. -/
def closedPointPicardClass {X : Scheme.{u}} (y : X) (hy : y ∈ closedPoints X)
    [IsEffectiveCartierDivisor
      (IdealSheafData.vanishingIdeal ⟨({y} : Set X), hy⟩).subschemeι] :
    X.PicardGroup :=
  Modules.picardClass
    (IdealSheafData.vanishingIdeal ⟨({y} : Set X), hy⟩).associatedSheaf

namespace Hom

/-- Every positive multiple of the Picard class of a closed effective Cartier
point lies outside the image of Picard pullback along the given morphism. -/
def HasNonextendablePointMultiples {X Y : Scheme.{u}} (restriction : X ⟶ Y)
    (y : X) (hy : y ∈ closedPoints X)
    [IsEffectiveCartierDivisor
      (IdealSheafData.vanishingIdeal ⟨({y} : Set X), hy⟩).subschemeι] : Prop :=
  ∀ n : ℕ, 0 < n →
    n • closedPointPicardClass y hy ∉ AddMonoidHom.range (picardPullback restriction)

/-- Nonextension of point multiples is equivalent to non-membership of every
positive multiple of the point class in the range of Picard pullback. -/
theorem hasNonextendablePointMultiples_iff {X Y : Scheme.{u}} (restriction : X ⟶ Y)
    (y : X) (hy : y ∈ closedPoints X)
    [IsEffectiveCartierDivisor
      (IdealSheafData.vanishingIdeal ⟨({y} : Set X), hy⟩).subschemeι] :
    HasNonextendablePointMultiples restriction y hy ↔
      ∀ n : ℕ, 0 < n →
        n • closedPointPicardClass y hy ∉ AddMonoidHom.range (picardPullback restriction) := sorry

end Hom

end AlgebraicGeometry.Scheme
