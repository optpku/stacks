module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.UniversalFirstOrder

/-!
# Checking universal first-order thickenings of algebraic spaces

A first-order thickening of algebraic spaces over `X` is universal if and only
if unique dotted lifts exist against first-order test thickenings whose
enlarged space is a scheme, equivalently an affine scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 76.15.1: a first-order thickening over `X` is universal if and only if
every compatible first-order test thickening whose enlarged space is a scheme
admits a unique lift over `X`. -/
@[stacks 0603]
#check (AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder.iff_existsUniqueLift_isScheme :
  ∀ {S : Scheme.{u}} {X Z Z' : AlgebraicSpace S}
    (i : Z ⟶ Z') (f : Z' ⟶ X) [IsFirstOrderThickening i],
    IsUniversalFirstOrder i f ↔
      ∀ {T T' : AlgebraicSpace S} (j : T ⟶ T') (b : T' ⟶ X)
        [IsScheme T'] [IsFirstOrderThickening j] (a : T ⟶ Z),
        a ≫ i ≫ f = j ≫ b →
          ExistsUnique fun a' : T' ⟶ Z' ↦ a ≫ i = j ≫ a' ∧ a' ≫ f = b)

/- The affine-scheme testing criterion of Lemma 76.15.1. -/
@[stacks 0603]
#check (AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder.iff_existsUniqueLift_isAffine :
  ∀ {S : Scheme.{u}} {X Z Z' : AlgebraicSpace S}
    (i : Z ⟶ Z') (f : Z' ⟶ X) [IsFirstOrderThickening i],
    IsUniversalFirstOrder i f ↔
      ∀ {T T' : AlgebraicSpace S} (j : T ⟶ T') (b : T' ⟶ X)
        [IsAffine T'] [IsFirstOrderThickening j] (a : T ⟶ Z),
        a ≫ i ≫ f = j ≫ b →
          ExistsUnique fun a' : T' ⟶ Z' ↦ a ≫ i = j ≫ a' ∧ a' ≫ f = b)

/- A first-order thickening `i : Z ⟶ Z'` over `X` is universal if and only if
unique dotted lifts exist against first-order test thickenings represented by
affine schemes over `S`. -/
#check (AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder.iff_existsUniqueLift_ofOver_isAffine :
  ∀ {S : Scheme.{u}} {X Z Z' : AlgebraicSpace S}
    (i : Z ⟶ Z') (f : Z' ⟶ X) [IsFirstOrderThickening i],
    IsUniversalFirstOrder i f ↔
      ∀ {T T' : Over S} [AlgebraicGeometry.IsAffine T'.left]
        (j : ofOver T ⟶ ofOver T') (b : ofOver T' ⟶ X)
        [IsFirstOrderThickening j] (a : ofOver T ⟶ Z),
        a ≫ i ≫ f = j ≫ b →
          ExistsUnique fun a' : ofOver T' ⟶ Z' ↦
            a ≫ i = j ≫ a' ∧ a' ≫ f = b)
