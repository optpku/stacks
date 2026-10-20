/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.BivariantClass.LocalizedExtension
public import ReasLib.AlgebraicGeometry.BivariantClass.ProperPushforward
public import ReasLib.AlgebraicGeometry.BivariantClass.Vanishing
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ClosedImmersion.Proper

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass.IsLocalizedExtension

/-- A localized extension on the second member of a set-theoretic closed cover
pushes forward to its ambient identity class when the first restriction vanishes. -/
theorem properPushforwardToTarget_eq
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {X₁ X₂ : Scheme.{u}}
    (i₁ : X₁ ⟶ X.left) (i₂ : X₂ ⟶ X.left)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (cover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ)
    {p : ℤ} {ambient : BivariantClass δ (𝟙 X) p}
    {ambient₂ : BivariantClass δ (𝟙 (Over.mk (i₂ ≫ X.hom))) p}
    {localized : BivariantClass δ
      (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X) p}
    (hlocalized : IsLocalizedExtension δ X i₁ i₂ p ambient₂ localized)
    (restrict_source :
      BivariantClass.restrict δ
          (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X)
          (𝟙 (Over.mk (i₂ ≫ X.hom))) (Over.homMk i₂)
          IsPullback.of_id_snd p ambient = ambient₂)
    (restrict_other :
      BivariantClass.Vanishes δ
        (BivariantClass.restrict δ
          (Over.homMk i₁ : Over.mk (i₁ ≫ X.hom) ⟶ X)
          (𝟙 (Over.mk (i₁ ≫ X.hom))) (Over.homMk i₁)
          IsPullback.of_id_snd p ambient)) :
    @BivariantClass.properPushforwardToTarget S _ δ _
        (Over.mk (i₂ ≫ X.hom)) X _ _
        (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X)
        (@AlgebraicGeometry.instIsProperOverHomMk X₂ X.left i₂
          ((IsClosedImmersion.iff_isProper_and_mono (f := i₂)).mp inferInstance).1
          S X.hom) p localized = ambient := sorry

end AlgebraicGeometry.BivariantClass.IsLocalizedExtension
