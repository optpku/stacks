/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.LocalizedChern.ClosedCover.Commutation

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.LocalizedChern

/- Lemma 42.47.6 (1): every homogeneous bivariant class on a locally finite-type
morphism into `X` commutes with a localized Newton class on the canonical base change. -/
@[stacks 0FAJ]
#check (AlgebraicGeometry.LocalizedChern.localizedNewtonClass_commute :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom]
    {X₁ X₂ : Scheme.{u}} (i₁ : X₁ ⟶ X.left) (i₂ : X₂ ⟶ X.left)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (cover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ)
    (E₂ : RingedSpace.ModuleDerived X₂.toRingedSpace)
    (perfect : RingedSpace.ModuleDerived.IsPerfect E₂) (p : ℕ)
    (restrictionZero : IsZero
      ((RingedSpace.modulePullbackDerived (pullback.snd i₁ i₂).toShHom).obj E₂))
    (newtonClass : RingedSpace.ModuleDerived X₂.toRingedSpace →
      (r : ℕ) → BivariantClass δ (𝟙 (Over.mk (i₂ ≫ X.hom))) (r : ℤ))
    (newtonClass_vanishes_after_pullback :
      ∀ {Z : Over S} [LocallyOfFiniteType Z.hom]
        (g₂ : Z ⟶ Over.mk (i₂ ≫ X.hom)) [LocallyOfFiniteType g₂.left],
        IsZero ((RingedSpace.modulePullbackDerived g₂.left.toShHom).obj E₂) →
          BivariantClass.Vanishes δ
            (BivariantClass.restrict δ g₂ (𝟙 Z) g₂ IsPullback.of_id_snd
              (p : ℤ) (newtonClass E₂ p)))
    (newtonClass_commute :
      ∀ {Z : Over S} [LocallyOfFiniteType Z.hom]
        (g₂ : Z ⟶ Over.mk (i₂ ≫ X.hom)) [LocallyOfFiniteType g₂.left]
        (q : ℤ) (c : BivariantClass δ g₂ q),
          BivariantClass.Commute δ g₂ (𝟙 (Over.mk (i₂ ≫ X.hom)))
            c (newtonClass E₂ p))
    (localized : BivariantClass δ
      (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X) (p : ℤ))
    (hlocalized : BivariantClass.IsLocalizedExtension δ X i₁ i₂ (p : ℤ)
      (newtonClass E₂ p) localized)
    {Y : Over S} [LocallyOfFiniteType Y.hom]
    (f : Y ⟶ X) [LocallyOfFiniteType f.left]
    (q : ℤ) (c : BivariantClass δ f q),
    BivariantClass.Commute δ f
      (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X) c localized)

/- Lemma 42.47.6 (2): every homogeneous bivariant class on a locally finite-type
morphism into `X` commutes with a localized Chern class on the canonical base change. -/
@[stacks 0FAJ]
#check (AlgebraicGeometry.LocalizedChern.localizedChernClass_commute :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom]
    {X₁ X₂ : Scheme.{u}} (i₁ : X₁ ⟶ X.left) (i₂ : X₂ ⟶ X.left)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (cover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ)
    (E₂ : RingedSpace.ModuleDerived X₂.toRingedSpace)
    (perfect : RingedSpace.ModuleDerived.IsPerfect E₂) (p : ℕ)
    (restrictionRank : Scheme.ModuleDerived.IsVectorBundleOfRankLTInDegree
      ((RingedSpace.modulePullbackDerived (pullback.snd i₁ i₂).toShHom).obj E₂) 0 p)
    (chernClass : RingedSpace.ModuleDerived X₂.toRingedSpace →
      (r : ℕ) → BivariantClass δ (𝟙 (Over.mk (i₂ ≫ X.hom))) (r : ℤ))
    (chernClass_vanishes_after_pullback :
      ∀ {Z : Over S} [LocallyOfFiniteType Z.hom]
        (g₂ : Z ⟶ Over.mk (i₂ ≫ X.hom)) [LocallyOfFiniteType g₂.left],
        Scheme.ModuleDerived.IsVectorBundleOfRankLTInDegree
            ((RingedSpace.modulePullbackDerived g₂.left.toShHom).obj E₂) 0 p →
          BivariantClass.Vanishes δ
            (BivariantClass.restrict δ g₂ (𝟙 Z) g₂ IsPullback.of_id_snd
              (p : ℤ) (chernClass E₂ p)))
    (chernClass_commute :
      ∀ {Z : Over S} [LocallyOfFiniteType Z.hom]
        (g₂ : Z ⟶ Over.mk (i₂ ≫ X.hom)) [LocallyOfFiniteType g₂.left]
        (q : ℤ) (c : BivariantClass δ g₂ q),
          BivariantClass.Commute δ g₂ (𝟙 (Over.mk (i₂ ≫ X.hom)))
            c (chernClass E₂ p))
    (localized : BivariantClass δ
      (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X) (p : ℤ))
    (hlocalized : BivariantClass.IsLocalizedExtension δ X i₁ i₂ (p : ℤ)
      (chernClass E₂ p) localized)
    {Y : Over S} [LocallyOfFiniteType Y.hom]
    (f : Y ⟶ X) [LocallyOfFiniteType f.left]
    (q : ℤ) (c : BivariantClass δ f q),
    BivariantClass.Commute δ f
      (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X) c localized)

end AlgebraicGeometry.LocalizedChern
