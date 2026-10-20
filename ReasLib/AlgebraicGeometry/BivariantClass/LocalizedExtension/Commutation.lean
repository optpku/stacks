/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.BivariantClass.LocalizedExtension
public import ReasLib.AlgebraicGeometry.BivariantClass.Commutation
public import ReasLib.AlgebraicGeometry.ChowCohomology.Restriction

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass.IsLocalizedExtension

/-- A localized extension of a universally commuting identity class commutes with every
homogeneous bivariant class into the covered target. -/
theorem commute
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {X₁ X₂ : Scheme.{u}}
    (i₁ : X₁ ⟶ X.left) (i₂ : X₂ ⟶ X.left)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (cover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ)
    {p : ℤ} {ambient : BivariantClass δ (𝟙 (Over.mk (i₂ ≫ X.hom))) p}
    {localized : BivariantClass δ
      (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X) p}
    (hlocalized : IsLocalizedExtension δ X i₁ i₂ p ambient localized)
    (ambient_commute :
      ∀ {Z : Over S} [LocallyOfFiniteType Z.hom]
        (g : Z ⟶ Over.mk (i₂ ≫ X.hom)) [LocallyOfFiniteType g.left]
        (q : ℤ) (c : BivariantClass δ g q),
          BivariantClass.Commute δ g (𝟙 (Over.mk (i₂ ≫ X.hom))) c ambient)
    {Y : Over S} [LocallyOfFiniteType Y.hom]
    (f : Y ⟶ X) [LocallyOfFiniteType f.left]
    (q : ℤ) (c : BivariantClass δ f q) :
    BivariantClass.Commute δ f
      (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X) c localized := sorry

end AlgebraicGeometry.BivariantClass.IsLocalizedExtension
