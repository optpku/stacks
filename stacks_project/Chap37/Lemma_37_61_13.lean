/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Pushforward.Perfect
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

/- Lemma 37.61.13: if `S` is Noetherian, `f : X ⟶ S` is a perfect proper morphism of
schemes, and `E` is a perfect object of `D(𝒪_X)`, then its derived pushforward is perfect in
`D(𝒪_S)`. -/
@[stacks 0B6G] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.pushforward_isPerfect_of_perfect_of_proper :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [IsNoetherian S] [IsProper f]
      [LocallyOfType RingHom.IsPerfectRingMap f]
      (E : RingedSpace.ModuleDerived X.toRingedSpace),
      RingedSpace.ModuleDerived.IsPerfect E →
        RingedSpace.ModuleDerived.IsPerfect
          ((RingedSpace.moduleDerivedPushforward f.toShHom).obj E))

end
