module

public import ReasLib.AlgebraicGeometry.BivariantClass.LocalizedExtension.BaseChange
public import ReasLib.AlgebraicGeometry.LocalizedChern.ClosedCover

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.LocalizedChern

/-- A localized Newton class for a two-member closed cover commutes with a locally
finite-type cartesian base change. -/
theorem localizedNewtonClass_eq_restrict
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X X' : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType X'.hom]
    {X₁ X₂ X₁' X₂' : Scheme.{u}}
    (i₁ : X₁ ⟶ X.left) (i₂ : X₂ ⟶ X.left)
    (i₁' : X₁' ⟶ X'.left) (i₂' : X₂' ⟶ X'.left)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    [IsClosedImmersion i₁'] [IsClosedImmersion i₂']
    (cover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ)
    (cover' : Set.range i₁'.base ∪ Set.range i₂'.base = Set.univ)
    (g : X' ⟶ X) [LocallyOfFiniteType g.left]
    (g₁ : Over.mk (i₁' ≫ X'.hom) ⟶ Over.mk (i₁ ≫ X.hom))
    (g₂ : Over.mk (i₂' ≫ X'.hom) ⟶ Over.mk (i₂ ≫ X.hom))
    [LocallyOfFiniteType g₁.left] [LocallyOfFiniteType g₂.left]
    (square₁ : IsPullback g₁.left i₁' i₁ g.left)
    (square₂ : IsPullback g₂.left
      (Over.homMk i₂' : Over.mk (i₂' ≫ X'.hom) ⟶ X').left
      (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X).left g.left)
    (E₂ : RingedSpace.ModuleDerived X₂.toRingedSpace)
    (perfect : RingedSpace.ModuleDerived.IsPerfect E₂)
    (perfect' : RingedSpace.ModuleDerived.IsPerfect
      ((RingedSpace.modulePullbackDerived g₂.left.toShHom).obj E₂))
    (p : ℕ)
    (restrictionZero : IsZero
      ((RingedSpace.modulePullbackDerived (pullback.snd i₁ i₂).toShHom).obj E₂))
    (restrictionZero' : IsZero
      ((RingedSpace.modulePullbackDerived (pullback.snd i₁' i₂').toShHom).obj
        ((RingedSpace.modulePullbackDerived g₂.left.toShHom).obj E₂)))
    (newtonClass : RingedSpace.ModuleDerived X₂.toRingedSpace →
      (q : ℕ) → BivariantClass δ (𝟙 (Over.mk (i₂ ≫ X.hom))) (q : ℤ))
    (newtonClass' : RingedSpace.ModuleDerived X₂'.toRingedSpace →
      (q : ℕ) → BivariantClass δ (𝟙 (Over.mk (i₂' ≫ X'.hom))) (q : ℤ))
    (newtonClass_vanishes_after_pullback :
      ∀ {Y : Over S} [LocallyOfFiniteType Y.hom]
        (h₂ : Y ⟶ Over.mk (i₂ ≫ X.hom)) [LocallyOfFiniteType h₂.left],
        IsZero ((RingedSpace.modulePullbackDerived h₂.left.toShHom).obj E₂) →
          BivariantClass.Vanishes δ
            (BivariantClass.restrict δ h₂ (𝟙 Y) h₂ IsPullback.of_id_snd
              (p : ℤ) (newtonClass E₂ p)))
    (newtonClass_vanishes_after_pullback' :
      ∀ {Y : Over S} [LocallyOfFiniteType Y.hom]
        (h₂ : Y ⟶ Over.mk (i₂' ≫ X'.hom)) [LocallyOfFiniteType h₂.left],
        IsZero ((RingedSpace.modulePullbackDerived h₂.left.toShHom).obj
          ((RingedSpace.modulePullbackDerived g₂.left.toShHom).obj E₂)) →
          BivariantClass.Vanishes δ
            (BivariantClass.restrict δ h₂ (𝟙 Y) h₂ IsPullback.of_id_snd (p : ℤ)
              (newtonClass'
                ((RingedSpace.modulePullbackDerived g₂.left.toShHom).obj E₂) p)))
    (ambient_baseChange :
      newtonClass' ((RingedSpace.modulePullbackDerived g₂.left.toShHom).obj E₂) p =
        BivariantClass.restrict δ g₂ (𝟙 (Over.mk (i₂' ≫ X'.hom))) g₂
          IsPullback.of_id_snd (p : ℤ) (newtonClass E₂ p))
    (localized : BivariantClass δ
      (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X) (p : ℤ))
    (localized' : BivariantClass δ
      (Over.homMk i₂' : Over.mk (i₂' ≫ X'.hom) ⟶ X') (p : ℤ))
    (hlocalized : BivariantClass.IsLocalizedExtension δ X i₁ i₂ (p : ℤ)
      (newtonClass E₂ p) localized)
    (hlocalized' : BivariantClass.IsLocalizedExtension δ X' i₁' i₂' (p : ℤ)
      (newtonClass' ((RingedSpace.modulePullbackDerived g₂.left.toShHom).obj E₂) p) localized') :
    localized' =
      BivariantClass.restrict δ g₂
        (Over.homMk i₂' : Over.mk (i₂' ≫ X'.hom) ⟶ X') g
        square₂ (p : ℤ) localized := sorry

/-- A localized Chern class for a two-member closed cover commutes with a locally
finite-type cartesian base change. -/
theorem localizedChernClass_eq_restrict
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X X' : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType X'.hom]
    {X₁ X₂ X₁' X₂' : Scheme.{u}}
    (i₁ : X₁ ⟶ X.left) (i₂ : X₂ ⟶ X.left)
    (i₁' : X₁' ⟶ X'.left) (i₂' : X₂' ⟶ X'.left)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    [IsClosedImmersion i₁'] [IsClosedImmersion i₂']
    (cover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ)
    (cover' : Set.range i₁'.base ∪ Set.range i₂'.base = Set.univ)
    (g : X' ⟶ X) [LocallyOfFiniteType g.left]
    (g₁ : Over.mk (i₁' ≫ X'.hom) ⟶ Over.mk (i₁ ≫ X.hom))
    (g₂ : Over.mk (i₂' ≫ X'.hom) ⟶ Over.mk (i₂ ≫ X.hom))
    [LocallyOfFiniteType g₁.left] [LocallyOfFiniteType g₂.left]
    (square₁ : IsPullback g₁.left i₁' i₁ g.left)
    (square₂ : IsPullback g₂.left
      (Over.homMk i₂' : Over.mk (i₂' ≫ X'.hom) ⟶ X').left
      (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X).left g.left)
    (E₂ : RingedSpace.ModuleDerived X₂.toRingedSpace)
    (perfect : RingedSpace.ModuleDerived.IsPerfect E₂)
    (perfect' : RingedSpace.ModuleDerived.IsPerfect
      ((RingedSpace.modulePullbackDerived g₂.left.toShHom).obj E₂))
    (p : ℕ)
    (restrictionRank : Scheme.ModuleDerived.IsVectorBundleOfRankLTInDegree
      ((RingedSpace.modulePullbackDerived (pullback.snd i₁ i₂).toShHom).obj E₂) 0 p)
    (restrictionRank' : Scheme.ModuleDerived.IsVectorBundleOfRankLTInDegree
      ((RingedSpace.modulePullbackDerived (pullback.snd i₁' i₂').toShHom).obj
        ((RingedSpace.modulePullbackDerived g₂.left.toShHom).obj E₂)) 0 p)
    (chernClass : RingedSpace.ModuleDerived X₂.toRingedSpace →
      (q : ℕ) → BivariantClass δ (𝟙 (Over.mk (i₂ ≫ X.hom))) (q : ℤ))
    (chernClass' : RingedSpace.ModuleDerived X₂'.toRingedSpace →
      (q : ℕ) → BivariantClass δ (𝟙 (Over.mk (i₂' ≫ X'.hom))) (q : ℤ))
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
        (h₂ : Y ⟶ Over.mk (i₂' ≫ X'.hom)) [LocallyOfFiniteType h₂.left],
        Scheme.ModuleDerived.IsVectorBundleOfRankLTInDegree
            ((RingedSpace.modulePullbackDerived h₂.left.toShHom).obj
              ((RingedSpace.modulePullbackDerived g₂.left.toShHom).obj E₂)) 0 p →
          BivariantClass.Vanishes δ
            (BivariantClass.restrict δ h₂ (𝟙 Y) h₂ IsPullback.of_id_snd (p : ℤ)
              (chernClass'
                ((RingedSpace.modulePullbackDerived g₂.left.toShHom).obj E₂) p)))
    (ambient_baseChange :
      chernClass' ((RingedSpace.modulePullbackDerived g₂.left.toShHom).obj E₂) p =
        BivariantClass.restrict δ g₂ (𝟙 (Over.mk (i₂' ≫ X'.hom))) g₂
          IsPullback.of_id_snd (p : ℤ) (chernClass E₂ p))
    (localized : BivariantClass δ
      (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X) (p : ℤ))
    (localized' : BivariantClass δ
      (Over.homMk i₂' : Over.mk (i₂' ≫ X'.hom) ⟶ X') (p : ℤ))
    (hlocalized : BivariantClass.IsLocalizedExtension δ X i₁ i₂ (p : ℤ)
      (chernClass E₂ p) localized)
    (hlocalized' : BivariantClass.IsLocalizedExtension δ X' i₁' i₂' (p : ℤ)
      (chernClass' ((RingedSpace.modulePullbackDerived g₂.left.toShHom).obj E₂) p) localized') :
    localized' =
      BivariantClass.restrict δ g₂
        (Over.homMk i₂' : Over.mk (i₂' ≫ X'.hom) ⟶ X') g
        square₂ (p : ℤ) localized := sorry

end AlgebraicGeometry.LocalizedChern
