/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Perfect.Pushforward
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

universe u

open AlgebraicGeometry.AlgebraicSpace.ModuleDerived

/- Lemma 76.47.5: let `S` be a scheme and let `Y` be a Noetherian algebraic space
over `S`. Let `f : X ⟶ Y` be a perfect proper morphism of algebraic spaces. If
`E` is a perfect object of `D(𝒪_X)`, then `(Modules.moduleDerivedPushforward f).obj E`
is a perfect object of `D(𝒪_Y)`. -/
@[stacks 0E4U] #check
  (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.pushforwardDerived_isPerfect_of_perfect_of_proper :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [Perfect f] [Proper f] [IsNoetherian Y] (E : ModuleDerived X),
      IsPerfect E → IsPerfect ((Modules.moduleDerivedPushforward f).obj E))
