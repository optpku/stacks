module

public import ReasLib.AlgebraicGeometry.BivariantClass.LocalizedExtension
public import ReasLib.AlgebraicGeometry.BivariantClass.Vanishing
public import ReasLib.AlgebraicGeometry.ChowGroup.ClosedCover
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.VectorBundle

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.LocalizedChern

/-- A perfect complex on the second member of a set-theoretic closed cover has a unique
localized Newton bivariant class when its restriction to the intersection vanishes. -/
theorem existsUniqueLocalizedNewtonClass
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom]
    {X₁ X₂ : Scheme.{u}} (i₁ : X₁ ⟶ X.left) (i₂ : X₂ ⟶ X.left)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (cover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ)
    (E₂ : RingedSpace.ModuleDerived X₂.toRingedSpace)
    (perfect : RingedSpace.ModuleDerived.IsPerfect E₂) (p : ℕ)
    (restrictionZero : IsZero
      ((RingedSpace.modulePullbackDerived (pullback.snd i₁ i₂).toShHom).obj E₂))
    (newtonClass : RingedSpace.ModuleDerived X₂.toRingedSpace →
      (q : ℕ) → BivariantClass δ (𝟙 (Over.mk (i₂ ≫ X.hom))) (q : ℤ))
    (newtonClass_vanishes_after_pullback :
      ∀ {Y : Over S} [LocallyOfFiniteType Y.hom]
        (g₂ : Y ⟶ Over.mk (i₂ ≫ X.hom)) [LocallyOfFiniteType g₂.left],
        IsZero ((RingedSpace.modulePullbackDerived g₂.left.toShHom).obj E₂) →
          BivariantClass.Vanishes δ
            (BivariantClass.restrict δ g₂ (𝟙 Y) g₂ IsPullback.of_id_snd
              (p : ℤ) (newtonClass E₂ p))) :
    ∃! localized : BivariantClass δ
        (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X) (p : ℤ),
      BivariantClass.IsLocalizedExtension δ X i₁ i₂ (p : ℤ)
        (newtonClass E₂ p) localized := sorry

/-- A perfect complex on the second member of a set-theoretic closed cover has a unique
localized Chern bivariant class when its restriction to the intersection is a degree-zero
vector bundle of pointwise rank below the specified degree. -/
theorem existsUniqueLocalizedChernClass
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom]
    {X₁ X₂ : Scheme.{u}} (i₁ : X₁ ⟶ X.left) (i₂ : X₂ ⟶ X.left)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (cover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ)
    (E₂ : RingedSpace.ModuleDerived X₂.toRingedSpace)
    (perfect : RingedSpace.ModuleDerived.IsPerfect E₂) (p : ℕ)
    (restrictionRank : Scheme.ModuleDerived.IsVectorBundleOfRankLTInDegree
      ((RingedSpace.modulePullbackDerived (pullback.snd i₁ i₂).toShHom).obj E₂) 0 p)
    (chernClass : RingedSpace.ModuleDerived X₂.toRingedSpace →
      (q : ℕ) → BivariantClass δ (𝟙 (Over.mk (i₂ ≫ X.hom))) (q : ℤ))
    (chernClass_vanishes_after_pullback :
      ∀ {Y : Over S} [LocallyOfFiniteType Y.hom]
        (g₂ : Y ⟶ Over.mk (i₂ ≫ X.hom)) [LocallyOfFiniteType g₂.left],
        Scheme.ModuleDerived.IsVectorBundleOfRankLTInDegree
            ((RingedSpace.modulePullbackDerived g₂.left.toShHom).obj E₂) 0 p →
          BivariantClass.Vanishes δ
            (BivariantClass.restrict δ g₂ (𝟙 Y) g₂ IsPullback.of_id_snd
              (p : ℤ) (chernClass E₂ p))) :
    ∃! localized : BivariantClass δ
        (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X) (p : ℤ),
      BivariantClass.IsLocalizedExtension δ X i₁ i₂ (p : ℤ)
        (chernClass E₂ p) localized := sorry

/-- Localized Newton bivariant classes for a perfect complex on the common second member of
two set-theoretic closed covers are independent of the first member of the cover. -/
theorem localizedNewtonClass_eq_of_closedCovers
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
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
      (newtonClass E₂ p) localized') :
    localized = localized' := sorry

/-- Localized Chern bivariant classes for a perfect complex on the common second member of
two set-theoretic closed covers are independent of the first member of the cover. -/
theorem localizedChernClass_eq_of_closedCovers
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
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
      (chernClass E₂ p) localized') :
    localized = localized' := sorry

end AlgebraicGeometry.LocalizedChern
