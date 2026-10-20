/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.LocalizedChern.Definedness
public import ReasLib.AlgebraicGeometry.LocalizedChern.GlobalProducer
public import ReasLib.AlgebraicGeometry.BivariantClass.PushforwardComp

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.LocalizedChern

/-- The localized bivariant class obtained by composing the graph deformation's localized
infinity class with its Gysin class and properly pushing forward to the closed center. -/
def graphLocalizedClass
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (classes : ChernClass.Theory δ X.hom)
    {E : RingedSpace.ModuleDerived X.left.toRingedSpace} {p : ℕ}
    {mode : RestrictionBehavior} (situation : Situation S δ X i E p mode) :
    BivariantClass δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ Over.mk X.hom) (p : ℤ) :=
  @BivariantClass.pushforwardComp S _ δ _
    (GlobalProducer.center δ X i E p mode situation) (Over.mk (i ≫ X.hom))
    (GlobalProducer.infinity δ X i E p mode situation) X
    (GlobalProducer.center_finiteType δ X i E p mode situation) inferInstance
    (GlobalProducer.infinity_finiteType δ X i E p mode situation) inferInstance
    (pullback.snd (GlobalProducer.infinityToX δ X i E p mode situation)
      (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ Over.mk X.hom))
    (by
      refine @instIsProperPullbackSnd _ _ _ _ _ ?_ _
      change IsProper
        ((BivariantClass.GysinAtInfinity.infinityInclusion X
            (GlobalProducer.b δ X i E p mode situation)).left ≫
          (BivariantClass.GysinAtInfinity.toX X
            (GlobalProducer.b δ X i E p mode situation)).left)
      infer_instance)
    (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ Over.mk X.hom)
    (GlobalProducer.centerMap δ X i E p mode situation)
    (GlobalProducer.infinityToX δ X i E p mode situation) pullback.condition (p : ℤ)
    (GlobalProducer.localizedInfinity δ X i classes E p mode situation)
    (@BivariantClass.gysinAtInfinity S _ _ δ _ X _
      (GlobalProducer.b δ X i E p mode situation)
      (GlobalProducer.b_proper δ X i E p mode situation)
      (GlobalProducer.b_affine_iso δ X i E p mode situation))

/-- The proper pushforward of the graph-localized Newton class is the ambient derived
Newton class. -/
theorem graphLocalizedClass_newton_pushforward
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (classes : ChernClass.Theory δ X.hom)
    {E : RingedSpace.ModuleDerived X.left.toRingedSpace} {p : ℕ}
    (situation : Situation S δ X i E p .vanishing) :
    BivariantClass.properPushforwardToTarget δ
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ Over.mk X.hom) (p : ℤ)
        (graphLocalizedClass i classes situation) =
      ChernClass.Derived.newtonClass δ X.hom classes E situation.perfect
        situation.isDefined p := sorry

/-- The proper pushforward of the graph-localized Chern class is the ambient derived
Chern class. -/
theorem graphLocalizedClass_chern_pushforward
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (classes : ChernClass.Theory δ X.hom)
    {E : RingedSpace.ModuleDerived X.left.toRingedSpace} {p : ℕ}
    (situation : Situation S δ X i E p .rankBound) :
    BivariantClass.properPushforwardToTarget δ
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ Over.mk X.hom) (p : ℤ)
        (graphLocalizedClass i classes situation) =
      ChernClass.Derived.totalClass δ X.hom classes E situation.perfect
        situation.isDefined p := sorry

end AlgebraicGeometry.LocalizedChern
