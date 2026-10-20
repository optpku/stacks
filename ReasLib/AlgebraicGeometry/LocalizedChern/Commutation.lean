/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.LocalizedChern.Classes
public import ReasLib.AlgebraicGeometry.BivariantClass.Commutation
public import ReasLib.AlgebraicGeometry.Scheme.Over.ClosedImmersion

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.LocalizedChern

/-- The canonical localized Newton class commutes with every homogeneous
bivariant class on a locally finite-type morphism into `X`. -/
theorem newtonClass_commute
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (classes : ChernClass.Theory δ X.hom)
    (E : RingedSpace.ModuleDerived X.left.toRingedSpace) (p : ℕ)
    (situation : Situation S δ X i E p .vanishing)
    {Y : Over S} [LocallyOfFiniteType Y.hom]
    (f : Y ⟶ X) [LocallyOfFiniteType f.left]
    (q : ℤ) (c : BivariantClass δ f q) :
    BivariantClass.Commute δ f
      (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) c
      (newtonClass i classes E situation.perfect situation.offCenter
        situation.finiteness p) := sorry

/-- The canonical localized Chern class commutes with every homogeneous
bivariant class on a locally finite-type morphism into `X`. -/
theorem chernClass_commute
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (classes : ChernClass.Theory δ X.hom)
    (E : RingedSpace.ModuleDerived X.left.toRingedSpace) (p : ℕ)
    (situation : Situation S δ X i E p .rankBound)
    {Y : Over S} [LocallyOfFiniteType Y.hom]
    (f : Y ⟶ X) [LocallyOfFiniteType f.left]
    (q : ℤ) (c : BivariantClass δ f q) :
    BivariantClass.Commute δ f
      (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) c
      (chernClass i classes E situation.perfect p situation.offCenter
        situation.finiteness) := sorry

end AlgebraicGeometry.LocalizedChern
