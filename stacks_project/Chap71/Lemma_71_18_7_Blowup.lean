module

public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap71.Lemma_71_6_12_Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Blowup

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

#check (AlgebraicGeometry.AlgebraicSpace.IsBlowup :
  {S : Scheme.{u}} → {X X' : AlgebraicSpace S} →
    (X' ⟶ X) → ClosedSubspace X → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.isEffectiveCartierDivisor_inverseImage_of_isBlowup :
  ∀ {S : Scheme.{u}} {X X' : AlgebraicSpace S} {f : X' ⟶ X} {Z : ClosedSubspace X}
    [IsBlowup f Z], IsEffectiveCartierDivisor (pullback.snd Z.ι f))

#check (AlgebraicGeometry.AlgebraicSpace.isBlowup_id_of_isEffectiveCartierDivisor :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (Z : ClosedSubspace X)
    [IsEffectiveCartierDivisor Z.ι], IsBlowup (𝟙 X) Z)

#check (AlgebraicGeometry.AlgebraicSpace.isBlowup_iff :
  ∀ {S : Scheme.{u}} {X X' : AlgebraicSpace S} (f : X' ⟶ X) (Z : ClosedSubspace X),
    IsBlowup f Z ↔
      IsEffectiveCartierDivisor (pullback.snd Z.ι f) ∧
        ∀ {Y : AlgebraicSpace S} (g : Y ⟶ X),
          IsEffectiveCartierDivisor (pullback.snd Z.ι g) →
            ExistsUnique fun h : Y ⟶ X' ↦ h ≫ f = g)

end AlgebraicGeometry.AlgebraicSpace
