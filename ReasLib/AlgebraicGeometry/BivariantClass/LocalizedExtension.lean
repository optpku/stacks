module

public import ReasLib.AlgebraicGeometry.BivariantClass.Restriction
public import ReasLib.AlgebraicGeometry.ChowGroup.ClosedCover

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass

/-- Agreement and vanishing on the two components of a closed cover, after every locally
finite-type base change, characterize a localized extension of an identity bivariant class. -/
structure IsLocalizedExtension
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom]
    {X₁ X₂ : Scheme.{u}} (i₁ : X₁ ⟶ X.left) (i₂ : X₂ ⟶ X.left)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂] (p : ℤ)
    (ambient : BivariantClass δ (𝟙 (Over.mk (i₂ ≫ X.hom))) p)
    (localized : BivariantClass δ
      (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X) p) : Prop where
  /-- On classes pushed forward from the second component, the localized class agrees with
  the base change of the ambient identity class. -/
  cap_source_pushforward :
    ∀ {Y Y₂ : Over S} [LocallyOfFiniteType Y.hom] [LocallyOfFiniteType Y₂.hom]
      (g : Y ⟶ X) [LocallyOfFiniteType g.left]
      (j₂ : Y₂ ⟶ Y) [IsProper j₂.left]
      (g₂ : Y₂ ⟶ Over.mk (i₂ ≫ X.hom)) [LocallyOfFiniteType g₂.left]
      (square₂ : IsPullback g₂.left j₂.left i₂ g.left)
      (k : ℤ) (α₂ : RelativeChow δ Y₂ k),
      localized.cap g₂ j₂ g square₂ k (ChowGroup.map δ Y₂ Y j₂ k α₂) =
        ambient.cap g₂ (𝟙 Y₂) g₂ IsPullback.of_id_snd k α₂
  /-- On classes pushed forward from the first component, the localized class vanishes. -/
  cap_other_pushforward :
    ∀ {Y Y₁ Y₂ : Over S}
      [LocallyOfFiniteType Y.hom] [LocallyOfFiniteType Y₁.hom]
      [LocallyOfFiniteType Y₂.hom]
      (g : Y ⟶ X) [LocallyOfFiniteType g.left]
      (j₁ : Y₁ ⟶ Y) [IsProper j₁.left]
      (g₁ : Y₁ ⟶ Over.mk (i₁ ≫ X.hom))
      (square₁ : IsPullback g₁.left j₁.left i₁ g.left)
      (j₂ : Y₂ ⟶ Y) (g₂ : Y₂ ⟶ Over.mk (i₂ ≫ X.hom))
      (square₂ : IsPullback g₂.left j₂.left i₂ g.left)
      (k : ℤ) (α₁ : RelativeChow δ Y₁ k),
      localized.cap g₂ j₂ g square₂ k (ChowGroup.map δ Y₁ Y j₁ k α₁) = 0

/-- Construct the localized-extension property from its agreement and vanishing cap laws. -/
def IsLocalizedExtension.ofCap
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom]
    {X₁ X₂ : Scheme.{u}} {i₁ : X₁ ⟶ X.left} {i₂ : X₂ ⟶ X.left}
    [IsClosedImmersion i₁] [IsClosedImmersion i₂] {p : ℤ}
    {ambient : BivariantClass δ (𝟙 (Over.mk (i₂ ≫ X.hom))) p}
    {localized : BivariantClass δ
      (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X) p}
    (cap_source_pushforward :
      ∀ {Y Y₂ : Over S} [LocallyOfFiniteType Y.hom] [LocallyOfFiniteType Y₂.hom]
        (g : Y ⟶ X) [LocallyOfFiniteType g.left]
        (j₂ : Y₂ ⟶ Y) [IsProper j₂.left]
        (g₂ : Y₂ ⟶ Over.mk (i₂ ≫ X.hom)) [LocallyOfFiniteType g₂.left]
        (square₂ : IsPullback g₂.left j₂.left i₂ g.left)
        (k : ℤ) (α₂ : RelativeChow δ Y₂ k),
        localized.cap g₂ j₂ g square₂ k (ChowGroup.map δ Y₂ Y j₂ k α₂) =
          ambient.cap g₂ (𝟙 Y₂) g₂ IsPullback.of_id_snd k α₂)
    (cap_other_pushforward :
      ∀ {Y Y₁ Y₂ : Over S}
        [LocallyOfFiniteType Y.hom] [LocallyOfFiniteType Y₁.hom]
        [LocallyOfFiniteType Y₂.hom]
        (g : Y ⟶ X) [LocallyOfFiniteType g.left]
        (j₁ : Y₁ ⟶ Y) [IsProper j₁.left]
        (g₁ : Y₁ ⟶ Over.mk (i₁ ≫ X.hom))
        (square₁ : IsPullback g₁.left j₁.left i₁ g.left)
        (j₂ : Y₂ ⟶ Y) (g₂ : Y₂ ⟶ Over.mk (i₂ ≫ X.hom))
        (square₂ : IsPullback g₂.left j₂.left i₂ g.left)
        (k : ℤ) (α₁ : RelativeChow δ Y₁ k),
        localized.cap g₂ j₂ g square₂ k (ChowGroup.map δ Y₁ Y j₁ k α₁) = 0) :
    IsLocalizedExtension δ X i₁ i₂ p ambient localized where
  cap_source_pushforward := cap_source_pushforward
  cap_other_pushforward := cap_other_pushforward

/-- The localized-extension property is equivalent to its agreement and vanishing cap laws. -/
theorem isLocalizedExtension_iff
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom]
    {X₁ X₂ : Scheme.{u}} {i₁ : X₁ ⟶ X.left} {i₂ : X₂ ⟶ X.left}
    [IsClosedImmersion i₁] [IsClosedImmersion i₂] {p : ℤ}
    {ambient : BivariantClass δ (𝟙 (Over.mk (i₂ ≫ X.hom))) p}
    {localized : BivariantClass δ
      (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X) p} :
    IsLocalizedExtension δ X i₁ i₂ p ambient localized ↔
      (∀ {Y Y₂ : Over S} [LocallyOfFiniteType Y.hom] [LocallyOfFiniteType Y₂.hom]
        (g : Y ⟶ X) [LocallyOfFiniteType g.left]
        (j₂ : Y₂ ⟶ Y) [IsProper j₂.left]
        (g₂ : Y₂ ⟶ Over.mk (i₂ ≫ X.hom)) [LocallyOfFiniteType g₂.left]
        (square₂ : IsPullback g₂.left j₂.left i₂ g.left)
        (k : ℤ) (α₂ : RelativeChow δ Y₂ k),
        localized.cap g₂ j₂ g square₂ k (ChowGroup.map δ Y₂ Y j₂ k α₂) =
          ambient.cap g₂ (𝟙 Y₂) g₂ IsPullback.of_id_snd k α₂) ∧
      (∀ {Y Y₁ Y₂ : Over S}
        [LocallyOfFiniteType Y.hom] [LocallyOfFiniteType Y₁.hom]
        [LocallyOfFiniteType Y₂.hom]
        (g : Y ⟶ X) [LocallyOfFiniteType g.left]
        (j₁ : Y₁ ⟶ Y) [IsProper j₁.left]
        (g₁ : Y₁ ⟶ Over.mk (i₁ ≫ X.hom))
        (square₁ : IsPullback g₁.left j₁.left i₁ g.left)
        (j₂ : Y₂ ⟶ Y) (g₂ : Y₂ ⟶ Over.mk (i₂ ≫ X.hom))
        (square₂ : IsPullback g₂.left j₂.left i₂ g.left)
        (k : ℤ) (α₁ : RelativeChow δ Y₁ k),
        localized.cap g₂ j₂ g square₂ k (ChowGroup.map δ Y₁ Y j₁ k α₁) = 0) := sorry

namespace IsLocalizedExtension

/-- Localized extensions of the same bivariant class relative to two set-theoretic closed
covers with a common second component are equal. -/
theorem eq_of_closedCovers
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {X₁ X₁' X₂ : Scheme.{u}}
    (i₁ : X₁ ⟶ X.left) (i₁' : X₁' ⟶ X.left) (i₂ : X₂ ⟶ X.left)
    [IsClosedImmersion i₁] [IsClosedImmersion i₁'] [IsClosedImmersion i₂]
    (cover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ)
    (cover' : Set.range i₁'.base ∪ Set.range i₂.base = Set.univ)
    {p : ℤ} {ambient : BivariantClass δ (𝟙 (Over.mk (i₂ ≫ X.hom))) p}
    {localized localized' : BivariantClass δ
      (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X) p}
    (hlocalized : IsLocalizedExtension δ X i₁ i₂ p ambient localized)
    (hlocalized' : IsLocalizedExtension δ X i₁' i₂ p ambient localized') :
    localized = localized' := sorry

end IsLocalizedExtension

end AlgebraicGeometry.BivariantClass
