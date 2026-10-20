module

public import ReasLib.AlgebraicGeometry.BivariantClass.LocalizedExtension
public import ReasLib.AlgebraicGeometry.LocalizedChern.CapPushforward
public import ReasLib.AlgebraicGeometry.LocalizedChern.DisjointSupport
public import ReasLib.AlgebraicGeometry.LocalizedChern.EnlargeCenter

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.LocalizedChern

open ChernClass.Derived

namespace Situation

/-- A set-theoretic closed cover transfers restriction behavior from its first member to the
open complement of its second member under the stated finiteness alternatives. -/
theorem ofClosedCover
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {X₁ X₂ : Scheme.{u}}
    (i₁ : X₁ ⟶ X.left) (i₂ : X₂ ⟶ X.left)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (cover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ)
    {E : RingedSpace.ModuleDerived X.left.toRingedSpace} {p : ℕ}
    {mode : RestrictionBehavior}
    (perfect : RingedSpace.ModuleDerived.IsPerfect E)
    (finiteness : TechnicalCondition X E)
    (restriction : RestrictionCondition i₁ E p mode) :
    Situation S δ X i₂ E p mode := sorry

end Situation

/-- A localized Newton class characterized on a closed cover agrees with the canonical class
when the derived restriction to the first component vanishes. -/
@[stacks 0FB8]
theorem localizedNewtonClass_eq_of_restriction
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {X₁ X₂ : Scheme.{u}}
    (i₁ : X₁ ⟶ X.left) (i₂ : X₂ ⟶ X.left)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (cover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ)
    (classes : ChernClass.Theory δ X.hom)
    (E : RingedSpace.ModuleDerived X.left.toRingedSpace) (p : ℕ)
    (perfect : RingedSpace.ModuleDerived.IsPerfect E)
    (finiteness : TechnicalCondition X E)
    (restrictionZero : RestrictionCondition i₁ E p .vanishing) :
    let situation : Situation S δ X i₂ E p .vanishing :=
      Situation.ofClosedCover i₁ i₂ cover perfect finiteness restrictionZero
    let E₂ := (RingedSpace.modulePullbackDerived i₂.toShHom).obj E
    ∀ (localized : BivariantClass δ
        (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X) (p : ℤ))
      (localized_spec : BivariantClass.IsLocalizedExtension δ X i₁ i₂ (p : ℤ)
        (ChernClass.Derived.newtonClass δ (i₂ ≫ X.hom)
          (classes.reanchor (Over.mk (i₂ ≫ X.hom))) E₂
          (RingedSpace.modulePullbackDerived_isPerfect i₂.toShHom E situation.perfect)
          (IsDefined.pullback i₂ situation.isDefined) p)
        localized),
      localized = newtonClass i₂ classes E situation.perfect situation.offCenter
        situation.finiteness p := sorry

/-- A localized Chern class characterized on a closed cover agrees with the canonical class
when the derived restriction to the first component has rank below `p` in degree zero. -/
@[stacks 0FB8]
theorem localizedChernClass_eq_of_restriction
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {X₁ X₂ : Scheme.{u}}
    (i₁ : X₁ ⟶ X.left) (i₂ : X₂ ⟶ X.left)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (cover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ)
    (classes : ChernClass.Theory δ X.hom)
    (E : RingedSpace.ModuleDerived X.left.toRingedSpace) (p : ℕ)
    (perfect : RingedSpace.ModuleDerived.IsPerfect E)
    (finiteness : TechnicalCondition X E)
    (restrictionRank : RestrictionCondition i₁ E p .rankBound) :
    let situation : Situation S δ X i₂ E p .rankBound :=
      Situation.ofClosedCover i₁ i₂ cover perfect finiteness restrictionRank
    let E₂ := (RingedSpace.modulePullbackDerived i₂.toShHom).obj E
    ∀ (localized : BivariantClass δ
        (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X) (p : ℤ))
      (localized_spec : BivariantClass.IsLocalizedExtension δ X i₁ i₂ (p : ℤ)
        (ChernClass.Derived.totalClass δ (i₂ ≫ X.hom)
          (classes.reanchor (Over.mk (i₂ ≫ X.hom))) E₂
          (RingedSpace.modulePullbackDerived_isPerfect i₂.toShHom E situation.perfect)
          (IsDefined.pullback i₂ situation.isDefined) p)
        localized),
      localized = chernClass i₂ classes E situation.perfect p situation.offCenter
        situation.finiteness := sorry

end AlgebraicGeometry.LocalizedChern
