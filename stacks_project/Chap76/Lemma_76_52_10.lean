/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Perfect.Pushforward.Relative

/-!
# Derived pushforward of relatively perfect complexes

Along a flat, proper morphism of finite presentation of algebraic spaces, derived
pushforward sends `Y`-perfect objects of `D(𝒪_X)` to perfect objects of `D(𝒪_Y)`,
and formation of that pushforward commutes with arbitrary cartesian base change.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory Limits

universe u

open AlgebraicGeometry.AlgebraicSpace.ModuleDerived

/- Lemma 76.52.10 (1): let `S` be a scheme and let `f : X ⟶ Y` be a flat, proper
morphism of finite presentation of algebraic spaces over `S`. If `E` in `D(𝒪_X)` is
`Y`-perfect, then `(Modules.moduleDerivedPushforward f).obj E` is a perfect object of
`D(𝒪_Y)`. -/
@[stacks 0DKX] #check
  (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.pushforwardDerived_isPerfect_of_isPerfectRelativeTo :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
      [Proper f] → [Flat f] → [FinitePresentation f] →
      ∀ (E : ModuleDerived X), IsPerfectRelativeTo f E →
        IsPerfect ((Modules.moduleDerivedPushforward f).obj E))

/- Lemma 76.52.10 (2): let `S` be a scheme and let `f : X ⟶ Y` be a flat, proper
morphism of finite presentation of algebraic spaces over `S`. If `E` in `D(𝒪_X)` is
`Y`-perfect, then for every cartesian square of algebraic spaces over `S` the
component of `DerivedBaseChange.map` at `E` is an isomorphism. -/
@[stacks 0DKX] #check
  (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.pushforwardDerived_baseChange_isIso_of_isPerfectRelativeTo :
    ∀ {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
      (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y),
      [Proper f] → [Flat f] → [FinitePresentation f] →
      ∀ (sq : IsPullback g' f' f g) (E : ModuleDerived X), IsPerfectRelativeTo f E →
        IsIso ((DerivedBaseChange.map (derivedPullbackPushforwardAdjunction f)
            (derivedPullbackPushforwardAdjunction f')
            (DerivedQCoh.cohomologyBaseChangeCartesianIso sq)).app E))
