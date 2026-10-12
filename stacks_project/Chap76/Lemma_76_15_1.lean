/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap66.Lemma_66_13_1_IsScheme
public import stacks_project.Chap67.Definition_67_20_2_Affine
public import stacks_project.Chap76.«76_15_0_1_Universal»

/-!
# Checking universal first-order thickenings of algebraic spaces

A first-order thickening of algebraic spaces over `X` is universal if and only
if unique dotted lifts exist against first-order test thickenings whose
enlarged space is a scheme, equivalently an affine scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder

/-- Lemma 76.15.1 (1): a first-order thickening `i : Z ⟶ Z'` over `X` is a
universal first-order thickening if and only if every diagram 76.15.0.1 with
`T'` a scheme admits a unique dotted arrow. -/
@[stacks 0603]
theorem iff_existsUniqueLift_isScheme {S : Scheme.{u}} {X Z Z' : AlgebraicSpace S}
    (i : Z ⟶ Z') (f : Z' ⟶ X) [IsFirstOrderThickening i] :
    IsUniversalFirstOrder i f ↔
      ∀ {T T' : AlgebraicSpace S} (j : T ⟶ T') (b : T' ⟶ X)
        [IsScheme T'] [IsFirstOrderThickening j] (a : T ⟶ Z),
        a ≫ i ≫ f = j ≫ b →
          ExistsUnique fun a' : T' ⟶ Z' ↦ a ≫ i = j ≫ a' ∧ a' ≫ f = b :=
  sorry

/-- Lemma 76.15.1 (2): a first-order thickening `i : Z ⟶ Z'` over `X` is a
universal first-order thickening if and only if every diagram 76.15.0.1 with
`T'` an affine scheme admits a unique dotted arrow. -/
@[stacks 0603]
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

end AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder
