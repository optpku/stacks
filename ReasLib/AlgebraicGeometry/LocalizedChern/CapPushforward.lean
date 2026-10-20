module

public import ReasLib.AlgebraicGeometry.LocalizedChern.BaseChange
public import ReasLib.AlgebraicGeometry.BivariantClass.Intersection
public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.Derived.Pullback
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Pullback

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.LocalizedChern

open ChernClass.Derived

/-- Capping the localized Newton class with the proper
pushforward of a Chow class on the center equals capping that class with the
ordinary Newton class of the derived restriction. -/
@[stacks 0FB4]
theorem newtonClass_cap_pushforward
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (classes : ChernClass.Theory δ X.hom)
    {E : RingedSpace.ModuleDerived X.left.toRingedSpace} {p : ℕ}
    (situation : Situation S δ X i E p .vanishing) (k : ℤ)
    (α : RelativeChow δ (Over.mk (i ≫ X.hom)) k) :
    (newtonClass i classes E situation.perfect situation.offCenter
        situation.finiteness p).cap
      (𝟙 (Over.mk (i ≫ X.hom))) (Over.homMk i) (𝟙 X)
      (IsPullback.id_horiz i) k
      (ChowGroup.map δ (Over.mk (i ≫ X.hom)) X (Over.homMk i) k α) =
    (ChernClass.Derived.newtonClass δ (i ≫ X.hom)
        (classes.reanchor (Over.mk (i ≫ X.hom)))
        ((RingedSpace.modulePullbackDerived i.toShHom).obj E)
        (RingedSpace.modulePullbackDerived_isPerfect i.toShHom E situation.perfect)
        (IsDefined.pullback i situation.isDefined) p).cap
      (𝟙 (Over.mk (i ≫ X.hom))) (𝟙 (Over.mk (i ≫ X.hom)))
      (𝟙 (Over.mk (i ≫ X.hom))) IsPullback.of_id_snd k α := sorry

/-- Capping the localized Chern class with the proper
pushforward of a Chow class on the center equals capping that class with the
ordinary Chern class of the derived restriction. -/
@[stacks 0FB4]
theorem chernClass_cap_pushforward
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (classes : ChernClass.Theory δ X.hom)
    {E : RingedSpace.ModuleDerived X.left.toRingedSpace} {p : ℕ}
    (situation : Situation S δ X i E p .rankBound) (k : ℤ)
    (α : RelativeChow δ (Over.mk (i ≫ X.hom)) k) :
    (chernClass i classes E situation.perfect p situation.offCenter
        situation.finiteness).cap
      (𝟙 (Over.mk (i ≫ X.hom))) (Over.homMk i) (𝟙 X)
      (IsPullback.id_horiz i) k
      (ChowGroup.map δ (Over.mk (i ≫ X.hom)) X (Over.homMk i) k α) =
    (ChernClass.Derived.totalClass δ (i ≫ X.hom)
        (classes.reanchor (Over.mk (i ≫ X.hom)))
        ((RingedSpace.modulePullbackDerived i.toShHom).obj E)
        (RingedSpace.modulePullbackDerived_isPerfect i.toShHom E situation.perfect)
        (IsDefined.pullback i situation.isDefined) p).cap
      (𝟙 (Over.mk (i ≫ X.hom))) (𝟙 (Over.mk (i ≫ X.hom)))
      (𝟙 (Over.mk (i ≫ X.hom))) IsPullback.of_id_snd k α := sorry

end AlgebraicGeometry.LocalizedChern
