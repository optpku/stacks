/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.BaseChange
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.HigherDirectImage
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Pushforward.Perfect.Tensor
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Rank

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpace.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- If a finitely presented module is flat over the base, has proper support, and all its
positive higher direct images vanish, then its pushforward is finite locally free. -/
theorem pushforward_isFiniteLocallyFree_of_vanishesAboveZero
    {X S : Scheme.{u}} (f : X ⟶ S) [Scheme.Hom.FinitePresentation f]
    (ℱ : X.Modules) [ℱ.IsFinitePresentation]
    [SheafOfModules.IsFlatOver ℱ f.toShHom] [HasProperSupportOver f ℱ]
    (hvanish : ∀ i : ℕ, 0 < i →
      IsZero (RingedSpace.Hom.higherDirectImageModule f.toShHom ℱ i)) :
    IsFiniteLocallyFree ((pushforward f).obj ℱ) := sorry

/-- Under the same hypotheses, the canonical underived pushforward comparison is invertible
after every cartesian base change. -/
theorem pushforward_baseChange_isIso_of_vanishesAboveZero
    {X S : Scheme.{u}} (f : X ⟶ S) [Scheme.Hom.FinitePresentation f]
    (ℱ : X.Modules) [ℱ.IsFinitePresentation]
    [SheafOfModules.IsFlatOver ℱ f.toShHom] [HasProperSupportOver f ℱ]
    (hvanish : ∀ i : ℕ, 0 < i →
      IsZero (RingedSpace.Hom.higherDirectImageModule f.toShHom ℱ i))
    {X' S' : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S') (g : S' ⟶ S)
    (sq : IsPullback g' f' f g) :
    IsIso ((BaseChange.map
      ((sq.toCommSq.map (Scheme.forgetToLocallyRingedSpace ⋙
        LocallyRingedSpace.forgetToSheafedSpace)) :
          CommSq g'.toShHom f'.toShHom f.toShHom g.toShHom)).app ℱ) := sorry

end AlgebraicGeometry.Scheme.Modules
