module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Normalization.Coproduct

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-! The reusable relative-normalization and binary-coproduct API is owned by
`ReasLib.AlgebraicGeometry.AlgebraicSpace.Normalization.Coproduct`. -/

#check (IsNormalization :
  ∀ {S : Scheme.{u}} {X Y X' : AlgebraicSpace S},
    (Y ⟶ X) → (Y ⟶ X') → (X' ⟶ X) → Prop)

#check (isNormalization_iff :
  ∀ {S : Scheme.{u}} {X Y X' : AlgebraicSpace S}
    (f : Y ⟶ X) (toN : Y ⟶ X') (fromN : X' ⟶ X),
    IsNormalization f toN fromN ↔
      toN ≫ fromN = f ∧ IsIntegralHom fromN ∧
        ∀ {Z : AlgebraicSpace S} (g : Y ⟶ Z) (π : Z ⟶ X) [IsIntegralHom π],
          f = g ≫ π → ∃! h : X' ⟶ Z, toN ≫ h = g ∧ h ≫ π = fromN)

#check (IsNormalization.of :
  ∀ {S : Scheme.{u}} {X Y X' : AlgebraicSpace S} {f : Y ⟶ X}
    {toN : Y ⟶ X'} {fromN : X' ⟶ X},
    (toN ≫ fromN = f) → IsIntegralHom fromN →
      (∀ {Z : AlgebraicSpace S} (g : Y ⟶ Z) (π : Z ⟶ X) [IsIntegralHom π],
        f = g ≫ π → ∃! h : X' ⟶ Z, toN ≫ h = g ∧ h ≫ π = fromN) →
      IsNormalization f toN fromN)

#check (IsNormalization.spec :
  ∀ {S : Scheme.{u}} {X Y X' : AlgebraicSpace S} {f : Y ⟶ X}
    {toN : Y ⟶ X'} {fromN : X' ⟶ X}, IsNormalization f toN fromN →
      toN ≫ fromN = f ∧ IsIntegralHom fromN ∧
        ∀ {Z : AlgebraicSpace S} (g : Y ⟶ Z) (π : Z ⟶ X) [IsIntegralHom π],
          f = g ≫ π → ∃! h : X' ⟶ Z, toN ≫ h = g ∧ h ≫ π = fromN)

#check (IsNormalization.existsUnique_hom :
  ∀ {S : Scheme.{u}} {X Y X₁ X₂ : AlgebraicSpace S}
    {f : Y ⟶ X} {to₁ : Y ⟶ X₁} {from₁ : X₁ ⟶ X}
    {to₂ : Y ⟶ X₂} {from₂ : X₂ ⟶ X},
    IsNormalization f to₁ from₁ → IsNormalization f to₂ from₂ →
      ∃! h : X₁ ⟶ X₂, to₁ ≫ h = to₂ ∧ h ≫ from₂ = from₁)

#check (normalizationCoproductSummand :
  ∀ {S : Scheme.{u}} (X₁ X₂ : AlgebraicSpace S),
    WalkingPair → AlgebraicSpace S)

#check (normalizationCoproduct :
  ∀ {S : Scheme.{u}} (X₁ X₂ : AlgebraicSpace S), AlgebraicSpace S)

#check (normalizationCoproductι₁ :
  ∀ {S : Scheme.{u}} (X₁ X₂ : AlgebraicSpace S),
    X₁ ⟶ normalizationCoproduct X₁ X₂)

#check (normalizationCoproductι₂ :
  ∀ {S : Scheme.{u}} (X₁ X₂ : AlgebraicSpace S),
    X₂ ⟶ normalizationCoproduct X₁ X₂)

#check (normalizationCoproductFrom :
  ∀ {S : Scheme.{u}} {X X₁ X₂ : AlgebraicSpace S},
    (X₁ ⟶ X) → (X₂ ⟶ X) → (normalizationCoproduct X₁ X₂ ⟶ X))

#check (AlgebraicGeometry.AlgebraicSpace.normalizationCoproductTo :
  ∀ {S : Scheme.{u}} {Y Y₁ Y₂ X₁ X₂ : AlgebraicSpace S}
    {ι₁ : Y₁ ⟶ Y} {ι₂ : Y₂ ⟶ Y}
    (hY : IsColimit (BinaryCofan.mk ι₁ ι₂)) (to₁ : Y₁ ⟶ X₁) (to₂ : Y₂ ⟶ X₂),
    Y ⟶ normalizationCoproduct X₁ X₂)

#check (normalizationCoproductι₁_from :
  ∀ {S : Scheme.{u}} {X X₁ X₂ : AlgebraicSpace S}
    (from₁ : X₁ ⟶ X) (from₂ : X₂ ⟶ X),
    normalizationCoproductι₁ X₁ X₂ ≫ normalizationCoproductFrom from₁ from₂ = from₁)

#check (normalizationCoproductι₂_from :
  ∀ {S : Scheme.{u}} {X X₁ X₂ : AlgebraicSpace S}
    (from₁ : X₁ ⟶ X) (from₂ : X₂ ⟶ X),
    normalizationCoproductι₂ X₁ X₂ ≫ normalizationCoproductFrom from₁ from₂ = from₂)

#check (ι₁_normalizationCoproductTo :
  ∀ {S : Scheme.{u}} {Y Y₁ Y₂ X₁ X₂ : AlgebraicSpace S}
    {ι₁ : Y₁ ⟶ Y} {ι₂ : Y₂ ⟶ Y}
    (hY : IsColimit (BinaryCofan.mk ι₁ ι₂)) (to₁ : Y₁ ⟶ X₁) (to₂ : Y₂ ⟶ X₂),
    ι₁ ≫ normalizationCoproductTo hY to₁ to₂ =
      to₁ ≫ normalizationCoproductι₁ X₁ X₂)

#check (ι₂_normalizationCoproductTo :
  ∀ {S : Scheme.{u}} {Y Y₁ Y₂ X₁ X₂ : AlgebraicSpace S}
    {ι₁ : Y₁ ⟶ Y} {ι₂ : Y₂ ⟶ Y}
    (hY : IsColimit (BinaryCofan.mk ι₁ ι₂)) (to₁ : Y₁ ⟶ X₁) (to₂ : Y₂ ⟶ X₂),
    ι₂ ≫ normalizationCoproductTo hY to₁ to₂ =
      to₂ ≫ normalizationCoproductι₂ X₁ X₂)

#check (isNormalization_coprod :
  ∀ {S : Scheme.{u}} {X Y Y₁ Y₂ X₁ X₂ : AlgebraicSpace S}
    (f : Y ⟶ X) (ι₁ : Y₁ ⟶ Y) (ι₂ : Y₂ ⟶ Y)
    (hY : IsColimit (BinaryCofan.mk ι₁ ι₂))
    [QuasiCompact f] [QuasiSeparated f]
    [QuasiCompact (ι₁ ≫ f)] [QuasiSeparated (ι₁ ≫ f)]
    [QuasiCompact (ι₂ ≫ f)] [QuasiSeparated (ι₂ ≫ f)]
    (to₁ : Y₁ ⟶ X₁) (from₁ : X₁ ⟶ X) (to₂ : Y₂ ⟶ X₂) (from₂ : X₂ ⟶ X),
    IsNormalization (ι₁ ≫ f) to₁ from₁ →
      IsNormalization (ι₂ ≫ f) to₂ from₂ →
        IsNormalization f (normalizationCoproductTo hY to₁ to₂)
          (normalizationCoproductFrom from₁ from₂))

end AlgebraicGeometry.AlgebraicSpace
