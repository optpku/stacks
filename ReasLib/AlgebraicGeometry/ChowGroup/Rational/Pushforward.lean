/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.Rational

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup

/-- Proper pushforward on rational total Chow homology. -/
noncomputable def rationalPushforward
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [IsProper f.left] :
    rationalChow δ X →+ rationalChow δ Y :=
  (LinearMap.rTensor ℚ (ChowGroup.Total.map δ f).toIntLinearMap).toAddMonoidHom

/-- Rational proper pushforward is scalar extension of integral proper pushforward. -/
theorem rationalPushforward_def
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [IsProper f.left] :
    rationalPushforward δ f =
      (LinearMap.rTensor ℚ (ChowGroup.Total.map δ f).toIntLinearMap).toAddMonoidHom := sorry

end AlgebraicGeometry.ChowGroup
