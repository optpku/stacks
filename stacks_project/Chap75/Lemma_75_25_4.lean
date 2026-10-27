/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Perfect.Pushforward.Flat

/-!
# Perfect derived pushforward along proper morphisms of finite presentation

Along a proper morphism of finite presentation of algebraic spaces, derived
pushforward of a perfect complex is perfect when the morphism is flat (part 1).
Derived pushforward of a finitely presented module flat over the target is
perfect as well (part 2). In both parts, formation commutes with arbitrary
cartesian base change.

The second part uses the authorized source correction: read "flat over Y" in
place of the printed "flat over S", consistently with the relative flatness
hypothesis of Lemma 75.25.1 used in the source proof.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory Limits
open CategoryTheory.DerivedCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

/- Lemma 75.25.4 (1): derived pushforward of a perfect complex along a flat
proper finitely presented morphism is perfect. -/
@[stacks 0CTM]
#check (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.pushforwardDerived_isPerfect_of_proper_flat :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Proper f] [FinitePresentation f] [Flat f]
    (E : ModuleDerived X) (hE : IsPerfect E),
    IsPerfect ((Modules.moduleDerivedPushforward f).obj E))

/- Lemma 75.25.4 (1): formation of the derived pushforward of a perfect complex
along a flat proper finitely presented morphism commutes with arbitrary
cartesian base change via the canonical derived mate. -/
@[stacks 0CTM]
#check (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.pushforwardDerived_baseChange_isIso_of_proper_flat :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {X' Y' : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [Proper f] [Flat f] [FinitePresentation f]
    (sq : IsPullback g' f' f g) (E : ModuleDerived X) (hE : IsPerfect E),
    IsIso ((DerivedBaseChange.map (derivedPullbackPushforwardAdjunction f)
        (derivedPullbackPushforwardAdjunction f')
        (DerivedQCoh.cohomologyBaseChangeCartesianIso sq)).app E))

/- Lemma 75.25.4 (2): derived pushforward of a finitely presented module flat
over Y along a proper finitely presented morphism is perfect. Here "flat over Y"
is the authorized correction of the printed "flat over S". -/
@[stacks 0CTM]
#check (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.pushforwardDerived_single_isPerfect_of_proper :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Proper f] [FinitePresentation f]
    (G : Modules X) (hG_fp : G.IsFinitePresentation)
    (hG_flat : ∀ x, Modules.flatOverAt G f x),
    IsPerfect ((Modules.moduleDerivedPushforward f).obj
      ((DerivedCategory.singleFunctor (Modules X) 0).obj G)))

/- Lemma 75.25.4 (2): formation of the derived pushforward of a finitely
presented module flat over Y commutes with arbitrary cartesian base change via
the canonical derived mate. -/
@[stacks 0CTM]
#check (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.pushforwardDerived_single_baseChange_isIso_of_proper :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {X' Y' : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [Proper f] [FinitePresentation f]
    (sq : IsPullback g' f' f g) (G : Modules X) (hG_fp : G.IsFinitePresentation)
    (hG_flat : ∀ x, Modules.flatOverAt G f x),
    IsIso ((DerivedBaseChange.map (derivedPullbackPushforwardAdjunction f)
        (derivedPullbackPushforwardAdjunction f')
        (DerivedQCoh.cohomologyBaseChangeCartesianIso sq)).app
      ((DerivedCategory.singleFunctor (Modules X) 0).obj G)))

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
