module

public import stacks_project.Chap42.Lemma_42_35_3_Vanishing
public import stacks_project.Chap42.Lemma_42_47_1_LocalizedClass
public import stacks_project.Chap42.Situation_42_50_1_LocalizedChern
public import ReasLib.AlgebraicGeometry.LocalizedChern.ClosedCover
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.LocalizedChern

/- Lemma 42.47.1 (1): if a perfect complex on the second member of a set-theoretic closed
cover restricts to zero on the intersection, then it has a unique localized Newton
bivariant class characterized on both cover components after every locally finite-type
base change. -/
@[stacks 0F9H]
#check (AlgebraicGeometry.LocalizedChern.existsUniqueLocalizedNewtonClass :
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
      (q : ℕ) → BivariantClass δ (𝟙 (Over.mk (i₂ ≫ X.hom))) (q : ℤ))
    (newtonClass_vanishes_after_pullback :
      ∀ {Y : Over S} [LocallyOfFiniteType Y.hom]
        (g₂ : Y ⟶ Over.mk (i₂ ≫ X.hom)) [LocallyOfFiniteType g₂.left],
        IsZero ((RingedSpace.modulePullbackDerived g₂.left.toShHom).obj E₂) →
          BivariantClass.Vanishes δ
            (BivariantClass.restrict δ g₂ (𝟙 Y) g₂ IsPullback.of_id_snd
              (p : ℤ) (newtonClass E₂ p))),
    ∃! localized : BivariantClass δ
        (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X) (p : ℤ),
      BivariantClass.IsLocalizedExtension δ X i₁ i₂ (p : ℤ)
        (newtonClass E₂ p) localized)

/- Lemma 42.47.1 (2): if the restriction of a perfect complex on the second member of a
set-theoretic closed cover is a degree-zero vector bundle of pointwise rank less than `p`,
then it has a unique localized Chern bivariant class characterized on both cover components
after every locally finite-type base change. -/
@[stacks 0F9H]
#check (AlgebraicGeometry.LocalizedChern.existsUniqueLocalizedChernClass :
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
      (q : ℕ) → BivariantClass δ (𝟙 (Over.mk (i₂ ≫ X.hom))) (q : ℤ))
    (chernClass_vanishes_after_pullback :
      ∀ {Y : Over S} [LocallyOfFiniteType Y.hom]
        (g₂ : Y ⟶ Over.mk (i₂ ≫ X.hom)) [LocallyOfFiniteType g₂.left],
        Scheme.ModuleDerived.IsVectorBundleOfRankLTInDegree
            ((RingedSpace.modulePullbackDerived g₂.left.toShHom).obj E₂) 0 p →
          BivariantClass.Vanishes δ
            (BivariantClass.restrict δ g₂ (𝟙 Y) g₂ IsPullback.of_id_snd
              (p : ℤ) (chernClass E₂ p))),
    ∃! localized : BivariantClass δ
        (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X) (p : ℤ),
      BivariantClass.IsLocalizedExtension δ X i₁ i₂ (p : ℤ)
        (chernClass E₂ p) localized)

end AlgebraicGeometry.LocalizedChern
