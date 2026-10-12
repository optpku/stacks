/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.BivariantClass.LocalizedExtension.Pushforward
public import ReasLib.AlgebraicGeometry.LocalizedChern.ClosedCover

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.LocalizedChern

/-- If a perfect complex restricts to zero on the first member of a set-theoretic closed
cover, the localized Newton class on the second member pushes forward to its ambient
Newton class. -/
theorem properPushforward_localizedNewtonClass
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {X₁ X₂ : Scheme.{u}}
    (i₁ : X₁ ⟶ X.left) (i₂ : X₂ ⟶ X.left)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (cover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ)
    (E : RingedSpace.ModuleDerived X.left.toRingedSpace)
    (perfect : RingedSpace.ModuleDerived.IsPerfect E) (p : ℕ)
    (restrictionZero : IsZero
      ((RingedSpace.modulePullbackDerived i₁.toShHom).obj E))
    (newtonClass : RingedSpace.ModuleDerived X.left.toRingedSpace →
      (q : ℕ) → BivariantClass δ (𝟙 X) (q : ℤ))
    (newtonClass₂ : RingedSpace.ModuleDerived X₂.toRingedSpace →
      (q : ℕ) → BivariantClass δ (𝟙 (Over.mk (i₂ ≫ X.hom))) (q : ℤ))
    (newtonClass_restrict :
      BivariantClass.restrict δ
          (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X)
          (𝟙 (Over.mk (i₂ ≫ X.hom))) (Over.homMk i₂)
          IsPullback.of_id_snd (p : ℤ) (newtonClass E p) =
        newtonClass₂ ((RingedSpace.modulePullbackDerived i₂.toShHom).obj E) p)
    (newtonClass_vanishes_on_X₁ :
      IsZero ((RingedSpace.modulePullbackDerived i₁.toShHom).obj E) →
        BivariantClass.Vanishes δ
          (BivariantClass.restrict δ
            (Over.homMk i₁ : Over.mk (i₁ ≫ X.hom) ⟶ X)
            (𝟙 (Over.mk (i₁ ≫ X.hom))) (Over.homMk i₁)
            IsPullback.of_id_snd (p : ℤ) (newtonClass E p)))
    (localized : BivariantClass δ
      (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X) (p : ℤ))
    (hlocalized : BivariantClass.IsLocalizedExtension δ X i₁ i₂ (p : ℤ)
      (newtonClass₂ ((RingedSpace.modulePullbackDerived i₂.toShHom).obj E) p) localized) :
    @BivariantClass.properPushforwardToTarget S _ δ _
        (Over.mk (i₂ ≫ X.hom)) X _ _
        (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X)
        (@AlgebraicGeometry.instIsProperOverHomMk X₂ X.left i₂
          ((IsClosedImmersion.iff_isProper_and_mono (f := i₂)).mp inferInstance).1
          S X.hom) (p : ℤ) localized = newtonClass E p := sorry

/-- If a perfect complex restricts on the first member of a set-theoretic closed cover to
a degree-zero vector bundle of rank below the specified degree, the localized Chern class
on the second member pushes forward to its ambient Chern class. -/
theorem properPushforward_localizedChernClass
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {X₁ X₂ : Scheme.{u}}
    (i₁ : X₁ ⟶ X.left) (i₂ : X₂ ⟶ X.left)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (cover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ)
    (E : RingedSpace.ModuleDerived X.left.toRingedSpace)
    (perfect : RingedSpace.ModuleDerived.IsPerfect E) (p : ℕ)
    (restrictionRank : Scheme.ModuleDerived.IsVectorBundleOfRankLTInDegree
      ((RingedSpace.modulePullbackDerived i₁.toShHom).obj E) 0 p)
    (chernClass : RingedSpace.ModuleDerived X.left.toRingedSpace →
      (q : ℕ) → BivariantClass δ (𝟙 X) (q : ℤ))
    (chernClass₂ : RingedSpace.ModuleDerived X₂.toRingedSpace →
      (q : ℕ) → BivariantClass δ (𝟙 (Over.mk (i₂ ≫ X.hom))) (q : ℤ))
    (chernClass_restrict :
      BivariantClass.restrict δ
          (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X)
          (𝟙 (Over.mk (i₂ ≫ X.hom))) (Over.homMk i₂)
          IsPullback.of_id_snd (p : ℤ) (chernClass E p) =
        chernClass₂ ((RingedSpace.modulePullbackDerived i₂.toShHom).obj E) p)
    (chernClass_vanishes_on_X₁ :
      Scheme.ModuleDerived.IsVectorBundleOfRankLTInDegree
          ((RingedSpace.modulePullbackDerived i₁.toShHom).obj E) 0 p →
        BivariantClass.Vanishes δ
          (BivariantClass.restrict δ
            (Over.homMk i₁ : Over.mk (i₁ ≫ X.hom) ⟶ X)
            (𝟙 (Over.mk (i₁ ≫ X.hom))) (Over.homMk i₁)
            IsPullback.of_id_snd (p : ℤ) (chernClass E p)))
    (localized : BivariantClass δ
      (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X) (p : ℤ))
    (hlocalized : BivariantClass.IsLocalizedExtension δ X i₁ i₂ (p : ℤ)
      (chernClass₂ ((RingedSpace.modulePullbackDerived i₂.toShHom).obj E) p) localized) :
    @BivariantClass.properPushforwardToTarget S _ δ _
        (Over.mk (i₂ ≫ X.hom)) X _ _
        (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X)
        (@AlgebraicGeometry.instIsProperOverHomMk X₂ X.left i₂
          ((IsClosedImmersion.iff_isProper_and_mono (f := i₂)).mp inferInstance).1
          S X.hom) (p : ℤ) localized = chernClass E p := sorry

end AlgebraicGeometry.LocalizedChern
