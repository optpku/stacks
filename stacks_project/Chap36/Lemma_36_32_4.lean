/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pushforward.FiniteLocallyFree

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpace.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Lemma 36.32.4 (1): if a finitely presented module is flat over the base, has proper
support, and all its positive higher direct images vanish, then its pushforward is finite
locally free. -/
@[stacks 0D4E] #check
  (AlgebraicGeometry.Scheme.Modules.pushforward_isFiniteLocallyFree_of_vanishesAboveZero :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [Scheme.Hom.FinitePresentation f]
      (ℱ : X.Modules) [ℱ.IsFinitePresentation]
      [SheafOfModules.IsFlatOver ℱ f.toShHom] [HasProperSupportOver f ℱ]
      (hvanish : ∀ i : ℕ, 0 < i →
        IsZero (RingedSpace.Hom.higherDirectImageModule f.toShHom ℱ i)),
      IsFiniteLocallyFree ((pushforward f).obj ℱ))

/- Lemma 36.32.4 (2): under the same hypotheses, formation of the pushforward commutes
with every cartesian base change: the canonical underived base-change component is invertible. -/
@[stacks 0D4E] #check
  (AlgebraicGeometry.Scheme.Modules.pushforward_baseChange_isIso_of_vanishesAboveZero :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [Scheme.Hom.FinitePresentation f]
      (ℱ : X.Modules) [ℱ.IsFinitePresentation]
      [SheafOfModules.IsFlatOver ℱ f.toShHom] [HasProperSupportOver f ℱ]
      (hvanish : ∀ i : ℕ, 0 < i →
        IsZero (RingedSpace.Hom.higherDirectImageModule f.toShHom ℱ i))
      {X' S' : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S') (g : S' ⟶ S)
      (sq : IsPullback g' f' f g),
      IsIso ((BaseChange.map
        ((sq.toCommSq.map (Scheme.forgetToLocallyRingedSpace ⋙
          LocallyRingedSpace.forgetToSheafedSpace)) :
            CommSq g'.toShHom f'.toShHom f.toShHom g.toShHom)).app ℱ))

end AlgebraicGeometry.Scheme.Modules
