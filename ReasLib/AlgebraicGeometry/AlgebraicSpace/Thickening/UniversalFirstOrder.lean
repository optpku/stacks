module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.FirstOrder
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IsScheme
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine

/-!
# Universal first-order thickenings of algebraic spaces

A first-order thickening of algebraic spaces over a base is universal when every
compatible solid map from another first-order thickening over the same base
extends uniquely to a morphism of thickenings.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A first-order thickening `i : Z ⟶ Z'` over `X` via `f : Z' ⟶ X` is universal
if every first-order thickening `j : T ⟶ T'` over `X` and solid map `a : T ⟶ Z`
extend uniquely to a dotted morphism `a' : T' ⟶ Z'` over `X`. -/
class IsUniversalFirstOrder {S : Scheme.{u}} {X Z Z' : AlgebraicSpace S}
    (i : Z ⟶ Z') (f : Z' ⟶ X) : Prop extends IsFirstOrderThickening i where
  /-- A solid map from a first-order thickening over `X` extends uniquely to a
  morphism of thickenings over `X`. -/
  existsUniqueLift {T T' : AlgebraicSpace S} (j : T ⟶ T') (b : T' ⟶ X)
      [IsFirstOrderThickening j] (a : T ⟶ Z)
      (h_solid : a ≫ i ≫ f = j ≫ b) :
      ExistsUnique fun a' : T' ⟶ Z' ↦ a ≫ i = j ≫ a' ∧ a' ≫ f = b

/-- A morphism of algebraic spaces is a universal first-order thickening over `X`
if and only if it is a first-order thickening and every solid diagram over `X`
admits a unique dotted lift. -/
theorem isUniversalFirstOrder_iff {S : Scheme.{u}} {X Z Z' : AlgebraicSpace S}
    (i : Z ⟶ Z') (f : Z' ⟶ X) :
    IsUniversalFirstOrder i f ↔
      IsFirstOrderThickening i ∧
        ∀ {T T' : AlgebraicSpace S} (j : T ⟶ T') (b : T' ⟶ X)
          [IsFirstOrderThickening j] (a : T ⟶ Z),
          a ≫ i ≫ f = j ≫ b →
            ExistsUnique fun a' : T' ⟶ Z' ↦ a ≫ i = j ≫ a' ∧ a' ≫ f = b :=
  sorry

namespace IsUniversalFirstOrder

/-- The identity morphism of an algebraic space is a universal first-order
thickening of itself over itself. -/
instance instId {S : Scheme.{u}} {X : AlgebraicSpace S} :
    IsUniversalFirstOrder (𝟙 X) (𝟙 X) :=
  sorry

/-- A universal first-order thickening of `Z` over `X` is unique up to a unique
morphism of thickenings over `X`. -/
theorem existsUnique_iso {S : Scheme.{u}} {X Z Z' W : AlgebraicSpace S}
    (i : Z ⟶ Z') (f : Z' ⟶ X) (j : Z ⟶ W) (g : W ⟶ X)
    [IsUniversalFirstOrder i f] [IsUniversalFirstOrder j g]
    (h_over : i ≫ f = j ≫ g) :
    ExistsUnique fun a' : Z' ⟶ W ↦ i ≫ a' = j ∧ a' ≫ g = f :=
  sorry

/-- A first-order thickening over `X` is universal if and only if every compatible
map from a first-order thickening whose enlarged space is a scheme admits a unique
lift over `X`. -/
theorem iff_existsUniqueLift_isScheme {S : Scheme.{u}} {X Z Z' : AlgebraicSpace S}
    (i : Z ⟶ Z') (f : Z' ⟶ X) [IsFirstOrderThickening i] :
    IsUniversalFirstOrder i f ↔
      ∀ {T T' : AlgebraicSpace S} (j : T ⟶ T') (b : T' ⟶ X)
        [IsScheme T'] [IsFirstOrderThickening j] (a : T ⟶ Z),
        a ≫ i ≫ f = j ≫ b →
          ExistsUnique fun a' : T' ⟶ Z' ↦ a ≫ i = j ≫ a' ∧ a' ≫ f = b :=
  sorry

/-- A first-order thickening over `X` is universal if and only if every compatible
map from a first-order thickening whose enlarged space is an affine scheme admits
a unique lift over `X`. -/
theorem iff_existsUniqueLift_isAffine {S : Scheme.{u}} {X Z Z' : AlgebraicSpace S}
    (i : Z ⟶ Z') (f : Z' ⟶ X) [IsFirstOrderThickening i] :
    IsUniversalFirstOrder i f ↔
      ∀ {T T' : AlgebraicSpace S} (j : T ⟶ T') (b : T' ⟶ X)
        [IsAffine T'] [IsFirstOrderThickening j] (a : T ⟶ Z),
        a ≫ i ≫ f = j ≫ b →
          ExistsUnique fun a' : T' ⟶ Z' ↦ a ≫ i = j ≫ a' ∧ a' ≫ f = b :=
  sorry

/-- A first-order thickening `i : Z ⟶ Z'` over `X` is universal if and only if
unique dotted lifts exist against first-order test thickenings represented by
affine schemes over `S`. -/
theorem iff_existsUniqueLift_ofOver_isAffine
    {S : Scheme.{u}} {X Z Z' : AlgebraicSpace S}
    (i : Z ⟶ Z') (f : Z' ⟶ X) [IsFirstOrderThickening i] :
    IsUniversalFirstOrder i f ↔
      ∀ {T T' : Over S} [AlgebraicGeometry.IsAffine T'.left]
        (j : ofOver T ⟶ ofOver T') (b : ofOver T' ⟶ X)
        [IsFirstOrderThickening j] (a : ofOver T ⟶ Z),
        a ≫ i ≫ f = j ≫ b →
          ExistsUnique fun a' : ofOver T' ⟶ Z' ↦
            a ≫ i = j ≫ a' ∧ a' ≫ f = b :=
  sorry

end IsUniversalFirstOrder

end AlgebraicGeometry.AlgebraicSpace
