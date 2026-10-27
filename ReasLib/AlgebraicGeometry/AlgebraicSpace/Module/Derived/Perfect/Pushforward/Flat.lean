/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.CohomologyBaseChange.Pushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FlatOver.BaseChange

/-!
# Perfect derived pushforward under flatness hypotheses

Derived pushforward along a flat proper finitely presented morphism preserves
perfect complexes and commutes with arbitrary cartesian base change. Without
flatness of the morphism, the same conclusions hold for finitely presented
modules flat over the target, viewed as complexes concentrated in degree zero.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory Limits
open CategoryTheory.DerivedCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- Derived pushforward of a perfect complex along a flat proper finitely
presented morphism of algebraic spaces is perfect. -/
theorem pushforwardDerived_isPerfect_of_proper_flat
    (f : X ⟶ Y) [Proper f] [FinitePresentation f] [Flat f]
    (E : ModuleDerived X) (hE : IsPerfect E) :
    IsPerfect ((Modules.moduleDerivedPushforward f).obj E) := sorry

/-- The canonical derived base-change map for a perfect complex along a flat
proper finitely presented morphism of algebraic spaces is an isomorphism for
every cartesian base change. -/
theorem pushforwardDerived_baseChange_isIso_of_proper_flat
    {X' Y' : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [Proper f] [Flat f] [FinitePresentation f]
    (sq : IsPullback g' f' f g) (E : ModuleDerived X) (hE : IsPerfect E) :
    IsIso ((DerivedBaseChange.map (derivedPullbackPushforwardAdjunction f)
        (derivedPullbackPushforwardAdjunction f')
        (DerivedQCoh.cohomologyBaseChangeCartesianIso sq)).app E) := sorry

/-- Derived pushforward of a finitely presented module flat over the target of a
proper finitely presented morphism of algebraic spaces is perfect when the module
is viewed as a complex concentrated in degree zero. -/
theorem pushforwardDerived_single_isPerfect_of_proper
    (f : X ⟶ Y) [Proper f] [FinitePresentation f]
    (G : Modules X) (hG_fp : G.IsFinitePresentation)
    (hG_flat : ∀ x, Modules.flatOverAt G f x) :
    IsPerfect ((Modules.moduleDerivedPushforward f).obj
      ((DerivedCategory.singleFunctor (Modules X) 0).obj G)) := sorry

/-- The canonical derived base-change map for a finitely presented module flat
over the target of a proper finitely presented morphism of algebraic spaces is
an isomorphism for every cartesian base change, with the module concentrated in
degree zero. -/
theorem pushforwardDerived_single_baseChange_isIso_of_proper
    {X' Y' : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [Proper f] [FinitePresentation f]
    (sq : IsPullback g' f' f g) (G : Modules X) (hG_fp : G.IsFinitePresentation)
    (hG_flat : ∀ x, Modules.flatOverAt G f x) :
    IsIso ((DerivedBaseChange.map (derivedPullbackPushforwardAdjunction f)
        (derivedPullbackPushforwardAdjunction f')
        (DerivedQCoh.cohomologyBaseChangeCartesianIso sq)).app
      ((DerivedCategory.singleFunctor (Modules X) 0).obj G)) := sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
