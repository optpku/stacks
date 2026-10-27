/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.PseudoCoherent.Pushforward

/-!
# Derived pushforward of pseudo-coherent complexes

Along a flat, proper morphism of finite presentation of algebraic spaces, derived
pushforward sends pseudo-coherent objects of `D(𝒪_X)` to pseudo-coherent objects of
`D(𝒪_Y)`, and formation of that pushforward commutes with arbitrary cartesian base
change.
-/

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory Limits

universe u

/- Lemma 75.25.5 (1): let `S` be a scheme and let `f : X ⟶ Y` be a flat, proper
morphism of finite presentation of algebraic spaces over `S`. If `E` in `D(𝒪_X)` is
pseudo-coherent, then `(Modules.moduleDerivedPushforward f).obj E` is a pseudo-coherent
object of `D(𝒪_Y)`. -/
@[stacks 0CTN] #check
  (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.PseudoCoherent.pushforward :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
      (f : X ⟶ Y) [Proper f] [Flat f] [FinitePresentation f]
      (E : ModuleDerived X) (hE : IsPseudoCoherent X E),
      IsPseudoCoherent Y ((Modules.moduleDerivedPushforward f).obj E))

/- Lemma 75.25.5 (2): let `S` be a scheme and let `f : X ⟶ Y` be a flat, proper
morphism of finite presentation of algebraic spaces over `S`. If `E` in `D(𝒪_X)` is
pseudo-coherent, then for every cartesian square of algebraic spaces over `S` the
component of `DerivedBaseChange.map` at `E` is an isomorphism. -/
@[stacks 0CTN] #check
  (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.PseudoCoherent.baseChange_isIso :
    ∀ {S : Scheme.{u}} {X Y X' Y' : AlgebraicSpace S}
      (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
      [Proper f] [Flat f] [FinitePresentation f]
      (sq : IsPullback g' f' f g) (E : ModuleDerived X) (hE : IsPseudoCoherent X E),
      IsIso ((DerivedBaseChange.map (derivedPullbackPushforwardAdjunction f)
          (derivedPullbackPushforwardAdjunction f')
          (DerivedQCoh.cohomologyBaseChangeCartesianIso sq)).app E))
