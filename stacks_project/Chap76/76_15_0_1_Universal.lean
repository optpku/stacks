module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.UniversalFirstOrder

/-!
# Universal first-order thickenings of algebraic spaces

A first-order thickening of algebraic spaces over a base is universal when every
compatible solid map from another first-order thickening over the same base
extends uniquely to a morphism of thickenings.
-/

open CategoryTheory AlgebraicGeometry

universe u

/- 76.15.0.1: the universal first-order thickening property and its companion API. -/
#check (AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder :
  {S : Scheme.{u}} → {X Z Z' : AlgebraicSpace S} → (Z ⟶ Z') → (Z' ⟶ X) → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.isUniversalFirstOrder_iff :
  ∀ {S : Scheme.{u}} {X Z Z' : AlgebraicSpace S} (i : Z ⟶ Z') (f : Z' ⟶ X),
    AlgebraicSpace.IsUniversalFirstOrder i f ↔
      AlgebraicSpace.IsFirstOrderThickening i ∧
        ∀ {T T' : AlgebraicSpace S} (j : T ⟶ T') (b : T' ⟶ X)
          [AlgebraicSpace.IsFirstOrderThickening j] (a : T ⟶ Z),
          a ≫ i ≫ f = j ≫ b →
            ExistsUnique fun a' : T' ⟶ Z' ↦ a ≫ i = j ≫ a' ∧ a' ≫ f = b)

#check (AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder.instId :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S},
    AlgebraicSpace.IsUniversalFirstOrder (𝟙 X) (𝟙 X))

#check (AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder.existsUnique_iso :
  ∀ {S : Scheme.{u}} {X Z Z' W : AlgebraicSpace S}
    (i : Z ⟶ Z') (f : Z' ⟶ X) (j : Z ⟶ W) (g : W ⟶ X)
    [AlgebraicSpace.IsUniversalFirstOrder i f] [AlgebraicSpace.IsUniversalFirstOrder j g],
    i ≫ f = j ≫ g →
      ExistsUnique fun a' : Z' ⟶ W ↦ i ≫ a' = j ∧ a' ≫ g = f)
