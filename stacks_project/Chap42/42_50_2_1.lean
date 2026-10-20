/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.LocalizedChern.Classes

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.LocalizedChern

/- 42.50.2.1: proper pushforward sends the canonical localized Newton class
`P_p(Z ⟶ X, E)` to the ambient derived Newton class `P_p(E)`. -/
@[stacks 0FB1] #check
  (AlgebraicGeometry.LocalizedChern.newtonClass_pushforward :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
      {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
      (i : Z ⟶ X.left) [IsClosedImmersion i]
      (classes : ChernClass.Theory δ X.hom)
      (E : RingedSpace.ModuleDerived X.left.toRingedSpace)
      (perfect : RingedSpace.ModuleDerived.IsPerfect E)
      (vanishing : IsZero (restrictAway i E)) (finiteness : TechnicalCondition X E)
      (p : ℕ),
      BivariantClass.properPushforwardToTarget δ
          (Over.homMk i rfl : Over.mk (i ≫ X.hom) ⟶ Over.mk X.hom) (p : ℤ)
          (newtonClass i classes E perfect vanishing finiteness p) =
        ChernClass.Derived.newtonClass δ X.hom classes E perfect
          ((Situation.vanishing perfect vanishing finiteness :
            Situation S δ X i E p .vanishing).isDefined) p)

/- Companion: proper pushforward sends the canonical localized Chern class
`c_p(Z ⟶ X, E)` to the ambient derived Chern class `c_p(E)`. -/
#check
  (AlgebraicGeometry.LocalizedChern.chernClass_pushforward :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
      {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
      (i : Z ⟶ X.left) [IsClosedImmersion i]
      (classes : ChernClass.Theory δ X.hom)
      (E : RingedSpace.ModuleDerived X.left.toRingedSpace)
      (perfect : RingedSpace.ModuleDerived.IsPerfect E) (p : ℕ)
      (rankBound : Scheme.ModuleDerived.IsVectorBundleOfRankLTInDegree
        (restrictAway i E) 0 p) (finiteness : TechnicalCondition X E),
      BivariantClass.properPushforwardToTarget δ
          (Over.homMk i rfl : Over.mk (i ≫ X.hom) ⟶ Over.mk X.hom) (p : ℤ)
          (chernClass i classes E perfect p rankBound finiteness) =
        ChernClass.Derived.totalClass δ X.hom classes E perfect
          ((Situation.rankBound perfect rankBound finiteness :
            Situation S δ X i E p .rankBound).isDefined) p)

end AlgebraicGeometry.LocalizedChern
