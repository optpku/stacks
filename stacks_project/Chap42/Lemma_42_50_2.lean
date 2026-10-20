/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.LocalizedChern.GraphClass
public import stacks_project.Chap42.Situation_42_50_1_LocalizedChern
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.LocalizedChern

/- Lemma 42.50.2 (1): the canonical graph-localized Newton class has the
ambient derived Newton class as its proper pushforward. -/
@[stacks 0FB2] #check (AlgebraicGeometry.LocalizedChern.graphLocalizedClass_newton_pushforward :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (classes : ChernClass.Theory δ X.hom)
    {E : RingedSpace.ModuleDerived X.left.toRingedSpace} {p : ℕ}
    (situation : Situation S δ X i E p .vanishing),
    BivariantClass.properPushforwardToTarget δ
        (Over.homMk i rfl : Over.mk (i ≫ X.hom) ⟶ Over.mk X.hom) (p : ℤ)
        (graphLocalizedClass i classes situation) =
      ChernClass.Derived.newtonClass δ X.hom classes E situation.perfect
        situation.isDefined p)

/- Lemma 42.50.2 (2): the canonical graph-localized Chern class has the
ambient derived Chern class as its proper pushforward. -/
@[stacks 0FB2] #check (AlgebraicGeometry.LocalizedChern.graphLocalizedClass_chern_pushforward :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (classes : ChernClass.Theory δ X.hom)
    {E : RingedSpace.ModuleDerived X.left.toRingedSpace} {p : ℕ}
    (situation : Situation S δ X i E p .rankBound),
    BivariantClass.properPushforwardToTarget δ
        (Over.homMk i rfl : Over.mk (i ≫ X.hom) ⟶ Over.mk X.hom) (p : ℤ)
        (graphLocalizedClass i classes situation) =
      ChernClass.Derived.totalClass δ X.hom classes E situation.perfect
        situation.isDefined p)

end AlgebraicGeometry.LocalizedChern
