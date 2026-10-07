module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import ReasLib.AlgebraicGeometry.BivariantClass.ProperPushforward
public import ReasLib.AlgebraicGeometry.LocalizedChern.ClosedCover

/-!
# Proper pushforward for localized classes on closed covers

This file records the behavior of localized Newton and Chern bivariant classes when the
second member of a set-theoretic closed cover is replaced by a closed subscheme.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.LocalizedChern

/-- For nested set-theoretic closed covers, proper pushforward of the localized Newton
class on the smaller second member is the localized Newton class on the larger member. -/
theorem properPushforward_restrictedLocalizedNewtonClass
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {X₁ X₁' X₂ X₂' : Scheme.{u}}
    (j₁ : X₁ ⟶ X₁') (i₁' : X₁' ⟶ X.left)
    (j₂ : X₂' ⟶ X₂) (i₂ : X₂ ⟶ X.left)
    [IsClosedImmersion j₁] [IsClosedImmersion i₁']
    [IsClosedImmersion j₂] [IsClosedImmersion i₂]
    (cover : Set.range (j₁ ≫ i₁').base ∪ Set.range i₂.base = Set.univ)
    (cover' : Set.range i₁'.base ∪ Set.range (j₂ ≫ i₂).base = Set.univ)
    (E₂ : RingedSpace.ModuleDerived X₂.toRingedSpace)
    (perfect : RingedSpace.ModuleDerived.IsPerfect E₂) (p : ℕ)
    (restrictionZero : IsZero
      ((RingedSpace.modulePullbackDerived (pullback.snd (j₁ ≫ i₁') i₂).toShHom).obj E₂))
    (restrictionZero' : IsZero
      ((RingedSpace.modulePullbackDerived (pullback.snd i₁' i₂).toShHom).obj E₂))
    (newtonClass : RingedSpace.ModuleDerived X₂.toRingedSpace →
      (q : ℕ) → BivariantClass δ (𝟙 (Over.mk (i₂ ≫ X.hom))) (q : ℤ))
    (newtonClass' : RingedSpace.ModuleDerived X₂'.toRingedSpace →
      (q : ℕ) → BivariantClass δ (𝟙 (Over.mk ((j₂ ≫ i₂) ≫ X.hom))) (q : ℤ))
    (newtonClass_vanishes_after_pullback :
      ∀ {Y : Over S} [LocallyOfFiniteType Y.hom]
        (h₂ : Y ⟶ Over.mk (i₂ ≫ X.hom)) [LocallyOfFiniteType h₂.left],
        IsZero ((RingedSpace.modulePullbackDerived h₂.left.toShHom).obj E₂) →
          BivariantClass.Vanishes δ
            (BivariantClass.restrict δ h₂ (𝟙 Y) h₂ IsPullback.of_id_snd
              (p : ℤ) (newtonClass E₂ p)))
    (newtonClass_vanishes_after_pullback' :
      ∀ {Y : Over S} [LocallyOfFiniteType Y.hom]
        (h₂ : Y ⟶ Over.mk ((j₂ ≫ i₂) ≫ X.hom)) [LocallyOfFiniteType h₂.left],
        IsZero ((RingedSpace.modulePullbackDerived h₂.left.toShHom).obj
          ((RingedSpace.modulePullbackDerived j₂.toShHom).obj E₂)) →
          BivariantClass.Vanishes δ
            (BivariantClass.restrict δ h₂ (𝟙 Y) h₂ IsPullback.of_id_snd (p : ℤ)
              (newtonClass'
                ((RingedSpace.modulePullbackDerived j₂.toShHom).obj E₂) p)))
    (ambient_baseChange :
      newtonClass' ((RingedSpace.modulePullbackDerived j₂.toShHom).obj E₂) p =
        BivariantClass.restrict δ
          (Over.homMk j₂ (Category.assoc j₂ i₂ X.hom).symm :
            Over.mk ((j₂ ≫ i₂) ≫ X.hom) ⟶ Over.mk (i₂ ≫ X.hom))
          (𝟙 (Over.mk ((j₂ ≫ i₂) ≫ X.hom)))
          (Over.homMk j₂ (Category.assoc j₂ i₂ X.hom).symm :
            Over.mk ((j₂ ≫ i₂) ≫ X.hom) ⟶ Over.mk (i₂ ≫ X.hom))
          IsPullback.of_id_snd (p : ℤ) (newtonClass E₂ p))
    (localized : BivariantClass δ
      (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X) (p : ℤ))
    (localized' : BivariantClass δ
      (Over.homMk (j₂ ≫ i₂) : Over.mk ((j₂ ≫ i₂) ≫ X.hom) ⟶ X) (p : ℤ))
    (hlocalized : BivariantClass.IsLocalizedExtension δ X (j₁ ≫ i₁') i₂ (p : ℤ)
      (newtonClass E₂ p) localized)
    (hlocalized' : BivariantClass.IsLocalizedExtension δ X i₁' (j₂ ≫ i₂) (p : ℤ)
      (newtonClass' ((RingedSpace.modulePullbackDerived j₂.toShHom).obj E₂) p) localized') :
    BivariantClass.properPushforward δ
        (Over.homMk j₂ (Category.assoc j₂ i₂ X.hom).symm :
          Over.mk ((j₂ ≫ i₂) ≫ X.hom) ⟶ Over.mk (i₂ ≫ X.hom))
        (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X) (p : ℤ)
        ((Over.homMk_eta
          ((Over.homMk j₂ (Category.assoc j₂ i₂ X.hom).symm :
              Over.mk ((j₂ ≫ i₂) ≫ X.hom) ⟶ Over.mk (i₂ ≫ X.hom)) ≫
            (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X))
          (Eq.refl ((j₂ ≫ i₂) ≫ X.hom))) ▸ localized') = localized := sorry

/-- For the closed cover induced on the larger second member, proper pushforward of the
localized Chern class on the smaller member is the ambient Chern class. -/
theorem properPushforward_restrictedLocalizedChernClass
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {X₁ X₁' X₂ X₂' : Scheme.{u}}
    (j₁ : X₁ ⟶ X₁') (i₁' : X₁' ⟶ X.left)
    (j₂ : X₂' ⟶ X₂) (i₂ : X₂ ⟶ X.left)
    [IsClosedImmersion j₁] [IsClosedImmersion i₁']
    [IsClosedImmersion j₂] [IsClosedImmersion i₂]
    (cover : Set.range (j₁ ≫ i₁').base ∪ Set.range i₂.base = Set.univ)
    (cover' : Set.range i₁'.base ∪ Set.range (j₂ ≫ i₂).base = Set.univ)
    (E₂ : RingedSpace.ModuleDerived X₂.toRingedSpace)
    (perfect : RingedSpace.ModuleDerived.IsPerfect E₂) (p : ℕ)
    (restrictionRank : Scheme.ModuleDerived.IsVectorBundleOfRankLTInDegree
      ((RingedSpace.modulePullbackDerived
        (pullback.snd (j₁ ≫ i₁') i₂).toShHom).obj E₂) 0 p)
    (restrictionRank' : Scheme.ModuleDerived.IsVectorBundleOfRankLTInDegree
      ((RingedSpace.modulePullbackDerived (pullback.snd i₁' i₂).toShHom).obj E₂) 0 p)
    (chernClass : RingedSpace.ModuleDerived X₂.toRingedSpace →
      (q : ℕ) → BivariantClass δ (𝟙 (Over.mk (i₂ ≫ X.hom))) (q : ℤ))
    (chernClass' : RingedSpace.ModuleDerived X₂'.toRingedSpace →
      (q : ℕ) → BivariantClass δ
        (𝟙 (Over.mk (j₂ ≫ (i₂ ≫ X.hom)))) (q : ℤ))
    (chernClass_vanishes_after_pullback :
      ∀ {Y : Over S} [LocallyOfFiniteType Y.hom]
        (h₂ : Y ⟶ Over.mk (i₂ ≫ X.hom)) [LocallyOfFiniteType h₂.left],
        Scheme.ModuleDerived.IsVectorBundleOfRankLTInDegree
            ((RingedSpace.modulePullbackDerived h₂.left.toShHom).obj E₂) 0 p →
          BivariantClass.Vanishes δ
            (BivariantClass.restrict δ h₂ (𝟙 Y) h₂ IsPullback.of_id_snd
              (p : ℤ) (chernClass E₂ p)))
    (chernClass_vanishes_after_pullback' :
      ∀ {Y : Over S} [LocallyOfFiniteType Y.hom]
        (h₂ : Y ⟶ Over.mk (j₂ ≫ (i₂ ≫ X.hom))) [LocallyOfFiniteType h₂.left],
        Scheme.ModuleDerived.IsVectorBundleOfRankLTInDegree
            ((RingedSpace.modulePullbackDerived h₂.left.toShHom).obj
              ((RingedSpace.modulePullbackDerived j₂.toShHom).obj E₂)) 0 p →
          BivariantClass.Vanishes δ
            (BivariantClass.restrict δ h₂ (𝟙 Y) h₂ IsPullback.of_id_snd (p : ℤ)
              (chernClass'
                ((RingedSpace.modulePullbackDerived j₂.toShHom).obj E₂) p)))
    (ambient_baseChange :
      chernClass' ((RingedSpace.modulePullbackDerived j₂.toShHom).obj E₂) p =
        BivariantClass.restrict δ
          (Over.homMk j₂ :
            Over.mk (j₂ ≫ (i₂ ≫ X.hom)) ⟶ Over.mk (i₂ ≫ X.hom))
          (𝟙 (Over.mk (j₂ ≫ (i₂ ≫ X.hom))))
          (Over.homMk j₂ :
            Over.mk (j₂ ≫ (i₂ ≫ X.hom)) ⟶ Over.mk (i₂ ≫ X.hom))
          IsPullback.of_id_snd (p : ℤ) (chernClass E₂ p))
    (localized' : BivariantClass δ
      (Over.homMk j₂ :
        Over.mk (j₂ ≫ (i₂ ≫ X.hom)) ⟶ Over.mk (i₂ ≫ X.hom)) (p : ℤ))
    (hlocalized' : @BivariantClass.IsLocalizedExtension S _ δ _
      (Over.mk (i₂ ≫ X.hom)) _ (pullback i₁' i₂) X₂'
      (pullback.snd i₁' i₂) j₂ (instIsClosedImmersionSndScheme i₁' i₂)
      (inferInstance : IsClosedImmersion j₂) (p : ℤ)
      (chernClass' ((RingedSpace.modulePullbackDerived j₂.toShHom).obj E₂) p) localized') :
    BivariantClass.properPushforward δ
        (Over.homMk j₂ :
          Over.mk (j₂ ≫ (i₂ ≫ X.hom)) ⟶ Over.mk (i₂ ≫ X.hom))
        (𝟙 (Over.mk (i₂ ≫ X.hom))) (p : ℤ)
        ((Category.comp_id
          (Over.homMk j₂ :
            Over.mk (j₂ ≫ (i₂ ≫ X.hom)) ⟶ Over.mk (i₂ ≫ X.hom))).symm ▸ localized') =
      chernClass E₂ p := sorry

end AlgebraicGeometry.LocalizedChern
