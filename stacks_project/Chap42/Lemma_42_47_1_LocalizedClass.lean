/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.BivariantClass.LocalizedExtension

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass

/- The reusable localized-extension predicate remains available through this compatibility
module. -/
#check (AlgebraicGeometry.BivariantClass.IsLocalizedExtension :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom]
    {X₁ X₂ : Scheme.{u}} (i₁ : X₁ ⟶ X.left) (i₂ : X₂ ⟶ X.left)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂] (p : ℤ)
    (ambient : BivariantClass δ (𝟙 (Over.mk (i₂ ≫ X.hom))) p)
    (localized : BivariantClass δ
      (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X) p), Prop)

/- The generated structure constructor remains available through this compatibility module. -/
#check (AlgebraicGeometry.BivariantClass.IsLocalizedExtension.mk :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom]
    {X₁ X₂ : Scheme.{u}} {i₁ : X₁ ⟶ X.left} {i₂ : X₂ ⟶ X.left}
    [IsClosedImmersion i₁] [IsClosedImmersion i₂] {p : ℤ}
    {ambient : BivariantClass δ (𝟙 (Over.mk (i₂ ≫ X.hom))) p}
    {localized : BivariantClass δ
      (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X) p},
    (∀ {Y Y₂ : Over S} [LocallyOfFiniteType Y.hom] [LocallyOfFiniteType Y₂.hom]
      (g : Y ⟶ X) [LocallyOfFiniteType g.left]
      (j₂ : Y₂ ⟶ Y) [IsProper j₂.left]
      (g₂ : Y₂ ⟶ Over.mk (i₂ ≫ X.hom)) [LocallyOfFiniteType g₂.left]
      (square₂ : IsPullback g₂.left j₂.left i₂ g.left)
      (k : ℤ) (α₂ : RelativeChow δ Y₂ k),
      localized.cap g₂ j₂ g square₂ k (ChowGroup.map δ Y₂ Y j₂ k α₂) =
        ambient.cap g₂ (𝟙 Y₂) g₂ IsPullback.of_id_snd k α₂) →
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
      localized.cap g₂ j₂ g square₂ k (ChowGroup.map δ Y₁ Y j₁ k α₁) = 0) →
    IsLocalizedExtension δ X i₁ i₂ p ambient localized)

/- The bundled cap-law specification remains available through this compatibility module. -/
#check (AlgebraicGeometry.BivariantClass.isLocalizedExtension_iff :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom]
    {X₁ X₂ : Scheme.{u}} {i₁ : X₁ ⟶ X.left} {i₂ : X₂ ⟶ X.left}
    [IsClosedImmersion i₁] [IsClosedImmersion i₂] {p : ℤ}
    {ambient : BivariantClass δ (𝟙 (Over.mk (i₂ ≫ X.hom))) p}
    {localized : BivariantClass δ
      (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X) p},
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
        localized.cap g₂ j₂ g square₂ k (ChowGroup.map δ Y₁ Y j₁ k α₁) = 0))

end AlgebraicGeometry.BivariantClass
