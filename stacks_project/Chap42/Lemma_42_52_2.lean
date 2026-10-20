/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.LocalizedChern.Commutation
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.LocalizedChern

/- Lemma 42.52.2 (1): the localized Newton class commutes with every homogeneous
bivariant class on a locally finite-type morphism into `X`. -/
@[stacks 0FBB] #check (AlgebraicGeometry.LocalizedChern.newtonClass_commute :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (classes : ChernClass.Theory δ X.hom)
    (E : RingedSpace.ModuleDerived X.left.toRingedSpace) (p : ℕ)
    (situation : Situation S δ X i E p .vanishing)
    {Y : Over S} [LocallyOfFiniteType Y.hom]
    (f : Y ⟶ X) [LocallyOfFiniteType f.left]
    (q : ℤ) (c : BivariantClass δ f q),
    BivariantClass.Commute δ f
      (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) c
      (newtonClass i classes E situation.perfect situation.offCenter
        situation.finiteness p))

/- Lemma 42.52.2 (2): the localized Chern class commutes with every homogeneous
bivariant class on a locally finite-type morphism into `X`. -/
@[stacks 0FBB] #check (AlgebraicGeometry.LocalizedChern.chernClass_commute :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (classes : ChernClass.Theory δ X.hom)
    (E : RingedSpace.ModuleDerived X.left.toRingedSpace) (p : ℕ)
    (situation : Situation S δ X i E p .rankBound)
    {Y : Over S} [LocallyOfFiniteType Y.hom]
    (f : Y ⟶ X) [LocallyOfFiniteType f.left]
    (q : ℤ) (c : BivariantClass δ f q),
    BivariantClass.Commute δ f
      (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) c
      (chernClass i classes E situation.perfect p situation.offCenter
        situation.finiteness))

end AlgebraicGeometry.LocalizedChern
