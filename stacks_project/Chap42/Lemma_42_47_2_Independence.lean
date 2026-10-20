/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.BivariantClass.LocalizedExtension

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

/- Localized extensions of the same bivariant class relative to two closed covers sharing
the second component agree. -/
#check (AlgebraicGeometry.BivariantClass.IsLocalizedExtension.eq_of_closedCovers :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {X₁ X₁' X₂ : Scheme.{u}}
    (i₁ : X₁ ⟶ X.left) (i₁' : X₁' ⟶ X.left) (i₂ : X₂ ⟶ X.left)
    [IsClosedImmersion i₁] [IsClosedImmersion i₁'] [IsClosedImmersion i₂]
    (cover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ)
    (cover' : Set.range i₁'.base ∪ Set.range i₂.base = Set.univ)
    {p : ℤ} {ambient : AlgebraicGeometry.BivariantClass δ
      (𝟙 (Over.mk (i₂ ≫ X.hom))) p}
    {localized localized' : AlgebraicGeometry.BivariantClass δ
      (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X) p},
    AlgebraicGeometry.BivariantClass.IsLocalizedExtension δ X i₁ i₂ p ambient localized →
      AlgebraicGeometry.BivariantClass.IsLocalizedExtension δ X i₁' i₂ p ambient localized' →
      localized = localized')
