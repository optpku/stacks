/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Coproduct
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Normalization
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation

/-!
# Coproducts of relative normalizations

The coproduct of two relative-normalization factorizations of the restrictions of
a morphism along a binary disjoint union is a relative-normalization factorization
of the original morphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The `WalkingPair`-indexed family whose coproduct is the disjoint union of two
algebraic spaces. -/
def normalizationCoproductSummand {S : Scheme.{u}} (X₁ X₂ : AlgebraicSpace S) :
    WalkingPair → AlgebraicSpace S
  | .left => X₁
  | .right => X₂

/-- The binary disjoint union of two algebraic spaces, as the sheaf coproduct indexed
by `WalkingPair`. -/
def normalizationCoproduct {S : Scheme.{u}} (X₁ X₂ : AlgebraicSpace S) :
    AlgebraicSpace S :=
  coproduct (normalizationCoproductSummand X₁ X₂)

/-- The inclusion of the first summand into `normalizationCoproduct X₁ X₂`. -/
def normalizationCoproductι₁ {S : Scheme.{u}} (X₁ X₂ : AlgebraicSpace S) :
    X₁ ⟶ normalizationCoproduct X₁ X₂ :=
  coproductι (normalizationCoproductSummand X₁ X₂) WalkingPair.left

/-- The inclusion of the second summand into `normalizationCoproduct X₁ X₂`. -/
def normalizationCoproductι₂ {S : Scheme.{u}} (X₁ X₂ : AlgebraicSpace S) :
    X₂ ⟶ normalizationCoproduct X₁ X₂ :=
  coproductι (normalizationCoproductSummand X₁ X₂) WalkingPair.right

/-- The map `X₁ ⨿ X₂ ⟶ X` induced by a pair of morphisms to `X`. -/
def normalizationCoproductFrom {S : Scheme.{u}} {X X₁ X₂ : AlgebraicSpace S}
    (from₁ : X₁ ⟶ X) (from₂ : X₂ ⟶ X) :
    normalizationCoproduct X₁ X₂ ⟶ X :=
  coproductDesc fun i ↦ match i with
    | WalkingPair.left => from₁
    | WalkingPair.right => from₂

/-- The map `Y₁ ⨿ Y₂ ⟶ X₁ ⨿ X₂` induced by a pair of morphisms on the summands. -/
def normalizationCoproductTo {S : Scheme.{u}} {Y Y₁ Y₂ X₁ X₂ : AlgebraicSpace S}
    {ι₁ : Y₁ ⟶ Y} {ι₂ : Y₂ ⟶ Y} (hY : IsColimit (BinaryCofan.mk ι₁ ι₂))
    (to₁ : Y₁ ⟶ X₁) (to₂ : Y₂ ⟶ X₂) :
    Y ⟶ normalizationCoproduct X₁ X₂ :=
  hY.desc (BinaryCofan.mk (to₁ ≫ normalizationCoproductι₁ X₁ X₂)
    (to₂ ≫ normalizationCoproductι₂ X₁ X₂))

/-- Postcomposing the first coproduct inclusion with `normalizationCoproductFrom`
recovers `from₁`. -/
theorem normalizationCoproductι₁_from {S : Scheme.{u}} {X X₁ X₂ : AlgebraicSpace S}
    (from₁ : X₁ ⟶ X) (from₂ : X₂ ⟶ X) :
    normalizationCoproductι₁ X₁ X₂ ≫ normalizationCoproductFrom from₁ from₂ = from₁ :=
  sorry

/-- Postcomposing the second coproduct inclusion with `normalizationCoproductFrom`
recovers `from₂`. -/
theorem normalizationCoproductι₂_from {S : Scheme.{u}} {X X₁ X₂ : AlgebraicSpace S}
    (from₁ : X₁ ⟶ X) (from₂ : X₂ ⟶ X) :
    normalizationCoproductι₂ X₁ X₂ ≫ normalizationCoproductFrom from₁ from₂ = from₂ :=
  sorry

/-- The first summand inclusion of `Y` followed by `normalizationCoproductTo` is
`to₁` followed by the first coproduct inclusion. -/
theorem ι₁_normalizationCoproductTo {S : Scheme.{u}} {Y Y₁ Y₂ X₁ X₂ : AlgebraicSpace S}
    {ι₁ : Y₁ ⟶ Y} {ι₂ : Y₂ ⟶ Y} (hY : IsColimit (BinaryCofan.mk ι₁ ι₂))
    (to₁ : Y₁ ⟶ X₁) (to₂ : Y₂ ⟶ X₂) :
    ι₁ ≫ normalizationCoproductTo hY to₁ to₂ =
      to₁ ≫ normalizationCoproductι₁ X₁ X₂ :=
  sorry

/-- The second summand inclusion of `Y` followed by `normalizationCoproductTo` is
`to₂` followed by the second coproduct inclusion. -/
theorem ι₂_normalizationCoproductTo {S : Scheme.{u}} {Y Y₁ Y₂ X₁ X₂ : AlgebraicSpace S}
    {ι₁ : Y₁ ⟶ Y} {ι₂ : Y₂ ⟶ Y} (hY : IsColimit (BinaryCofan.mk ι₁ ι₂))
    (to₁ : Y₁ ⟶ X₁) (to₂ : Y₂ ⟶ X₂) :
    ι₂ ≫ normalizationCoproductTo hY to₁ to₂ =
      to₂ ≫ normalizationCoproductι₂ X₁ X₂ :=
  sorry

/-- The coproduct of two relative-normalization factorizations of the restrictions of
a quasi-compact and quasi-separated morphism along a binary disjoint union is a
relative-normalization factorization of the original morphism. -/
theorem isNormalization_coprod {S : Scheme.{u}} {X Y Y₁ Y₂ X₁ X₂ : AlgebraicSpace S}
    (f : Y ⟶ X) (ι₁ : Y₁ ⟶ Y) (ι₂ : Y₂ ⟶ Y)
    (hY : IsColimit (BinaryCofan.mk ι₁ ι₂))
    [QuasiCompact f] [QuasiSeparated f]
    [QuasiCompact (ι₁ ≫ f)] [QuasiSeparated (ι₁ ≫ f)]
    [QuasiCompact (ι₂ ≫ f)] [QuasiSeparated (ι₂ ≫ f)]
    (to₁ : Y₁ ⟶ X₁) (from₁ : X₁ ⟶ X) (to₂ : Y₂ ⟶ X₂) (from₂ : X₂ ⟶ X)
    (h₁ : IsNormalization (ι₁ ≫ f) to₁ from₁)
    (h₂ : IsNormalization (ι₂ ≫ f) to₂ from₂) :
    IsNormalization f (normalizationCoproductTo hY to₁ to₂)
      (normalizationCoproductFrom from₁ from₂) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
