module

import ReasLib.AlgebraicGeometry.LocalizedChern.ClosedCover
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.LocalizedChern

/- Lemma 42.47.2 (1): the localized Newton bivariant class associated to a perfect complex
on the fixed second component is independent of the first member of the closed cover. -/
@[stacks 0FAH] #check
  (AlgebraicGeometry.LocalizedChern.localizedNewtonClass_eq_of_closedCovers :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {X₁ X₁' X₂ : Scheme.{u}}
    (i₁ : X₁ ⟶ X.left) (i₁' : X₁' ⟶ X.left) (i₂ : X₂ ⟶ X.left)
    [IsClosedImmersion i₁] [IsClosedImmersion i₁'] [IsClosedImmersion i₂]
    (cover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ)
    (cover' : Set.range i₁'.base ∪ Set.range i₂.base = Set.univ)
    (E₂ : RingedSpace.ModuleDerived X₂.toRingedSpace)
    (perfect : RingedSpace.ModuleDerived.IsPerfect E₂) (p : ℕ)
    (restrictionZero : IsZero
      ((RingedSpace.modulePullbackDerived (pullback.snd i₁ i₂).toShHom).obj E₂))
    (restrictionZero' : IsZero
      ((RingedSpace.modulePullbackDerived (pullback.snd i₁' i₂).toShHom).obj E₂))
    (newtonClass : RingedSpace.ModuleDerived X₂.toRingedSpace →
      (q : ℕ) → BivariantClass δ (𝟙 (Over.mk (i₂ ≫ X.hom))) (q : ℤ))
    (newtonClass_vanishes_after_pullback :
      ∀ {Y : Over S} [LocallyOfFiniteType Y.hom]
        (g₂ : Y ⟶ Over.mk (i₂ ≫ X.hom)) [LocallyOfFiniteType g₂.left],
        IsZero ((RingedSpace.modulePullbackDerived g₂.left.toShHom).obj E₂) →
          BivariantClass.Vanishes δ
            (BivariantClass.restrict δ g₂ (𝟙 Y) g₂ IsPullback.of_id_snd
              (p : ℤ) (newtonClass E₂ p)))
    (localized localized' : BivariantClass δ
      (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X) (p : ℤ))
    (hlocalized : BivariantClass.IsLocalizedExtension δ X i₁ i₂ (p : ℤ)
      (newtonClass E₂ p) localized)
    (hlocalized' : BivariantClass.IsLocalizedExtension δ X i₁' i₂ (p : ℤ)
      (newtonClass E₂ p) localized'),
    localized = localized')

/- Lemma 42.47.2 (2): the localized Chern bivariant class associated to a perfect complex
on the fixed second component is independent of the first member of the closed cover. -/
@[stacks 0FAH] #check
  (AlgebraicGeometry.LocalizedChern.localizedChernClass_eq_of_closedCovers :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {X₁ X₁' X₂ : Scheme.{u}}
    (i₁ : X₁ ⟶ X.left) (i₁' : X₁' ⟶ X.left) (i₂ : X₂ ⟶ X.left)
    [IsClosedImmersion i₁] [IsClosedImmersion i₁'] [IsClosedImmersion i₂]
    (cover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ)
    (cover' : Set.range i₁'.base ∪ Set.range i₂.base = Set.univ)
    (E₂ : RingedSpace.ModuleDerived X₂.toRingedSpace)
    (perfect : RingedSpace.ModuleDerived.IsPerfect E₂) (p : ℕ)
    (restrictionRank : Scheme.ModuleDerived.IsVectorBundleOfRankLTInDegree
      ((RingedSpace.modulePullbackDerived (pullback.snd i₁ i₂).toShHom).obj E₂) 0 p)
    (restrictionRank' : Scheme.ModuleDerived.IsVectorBundleOfRankLTInDegree
      ((RingedSpace.modulePullbackDerived (pullback.snd i₁' i₂).toShHom).obj E₂) 0 p)
    (chernClass : RingedSpace.ModuleDerived X₂.toRingedSpace →
      (q : ℕ) → BivariantClass δ (𝟙 (Over.mk (i₂ ≫ X.hom))) (q : ℤ))
    (chernClass_vanishes_after_pullback :
      ∀ {Y : Over S} [LocallyOfFiniteType Y.hom]
        (g₂ : Y ⟶ Over.mk (i₂ ≫ X.hom)) [LocallyOfFiniteType g₂.left],
        Scheme.ModuleDerived.IsVectorBundleOfRankLTInDegree
            ((RingedSpace.modulePullbackDerived g₂.left.toShHom).obj E₂) 0 p →
          BivariantClass.Vanishes δ
            (BivariantClass.restrict δ g₂ (𝟙 Y) g₂ IsPullback.of_id_snd
              (p : ℤ) (chernClass E₂ p)))
    (localized localized' : BivariantClass δ
      (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X) (p : ℤ))
    (hlocalized : BivariantClass.IsLocalizedExtension δ X i₁ i₂ (p : ℤ)
      (chernClass E₂ p) localized)
    (hlocalized' : BivariantClass.IsLocalizedExtension δ X i₁' i₂ (p : ℤ)
      (chernClass E₂ p) localized'),
    localized = localized')

end AlgebraicGeometry.LocalizedChern
