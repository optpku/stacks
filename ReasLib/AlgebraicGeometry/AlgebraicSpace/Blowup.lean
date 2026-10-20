module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Closed.InverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.EffectiveCartier

/-!
# Blowups of algebraic spaces in closed subspaces

A morphism of algebraic spaces is a blowup in a closed subspace when the
inverse image of the center is an effective Cartier divisor and the morphism
is terminal among maps to the base with that property.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism `f : X' ⟶ X` is a blowup of `X` in the closed subspace `Z` when the
inverse image of `Z` is an effective Cartier divisor and `f` is terminal among
morphisms to `X` with that property. -/
class IsBlowup {S : Scheme.{u}} {X X' : AlgebraicSpace S}
    (f : X' ⟶ X) (Z : ClosedSubspace X) : Prop where
  /-- The inverse image of the center is an effective Cartier divisor. -/
  inverseImage_isEffectiveCartier : IsEffectiveCartierDivisor (pullback.snd Z.ι f)
  /-- The blowup is terminal among morphisms to `X` whose inverse image of `Z` is an
  effective Cartier divisor. -/
  lift_unique {Y : AlgebraicSpace S} (g : Y ⟶ X)
      (hg : IsEffectiveCartierDivisor (pullback.snd Z.ι g)) :
    ExistsUnique fun h : Y ⟶ X' ↦ h ≫ f = g

/-- The inverse image of the center of a blowup is an effective Cartier divisor. -/
def isEffectiveCartierDivisor_inverseImage_of_isBlowup
    {S : Scheme.{u}} {X X' : AlgebraicSpace S} {f : X' ⟶ X} {Z : ClosedSubspace X}
    [h : IsBlowup f Z] : IsEffectiveCartierDivisor (pullback.snd Z.ι f) :=
  h.inverseImage_isEffectiveCartier

/-- A morphism is a blowup in `Z` exactly when the inverse image of `Z` is an
effective Cartier divisor and the morphism is terminal among such maps. -/
theorem isBlowup_iff {S : Scheme.{u}} {X X' : AlgebraicSpace S}
    (f : X' ⟶ X) (Z : ClosedSubspace X) :
    IsBlowup f Z ↔
      IsEffectiveCartierDivisor (pullback.snd Z.ι f) ∧
        ∀ {Y : AlgebraicSpace S} (g : Y ⟶ X),
          IsEffectiveCartierDivisor (pullback.snd Z.ι g) →
            ExistsUnique fun h : Y ⟶ X' ↦ h ≫ f = g :=
  sorry

/-- The identity of `X` is the blowup of `X` in an effective Cartier divisor. -/
def isBlowup_id_of_isEffectiveCartierDivisor
    {S : Scheme.{u}} {X : AlgebraicSpace S} (Z : ClosedSubspace X)
    [IsEffectiveCartierDivisor Z.ι] : IsBlowup (𝟙 X) Z :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
