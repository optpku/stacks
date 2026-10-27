/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Perfect.Relative
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.CohomologyBaseChange.Pushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation

/-!
# Derived pushforward of relatively perfect complexes

For flat proper finitely presented morphisms of algebraic spaces, derived
pushforward preserves relative perfectness as absolute perfectness and commutes
with arbitrary base change.
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

/-- The derived pushforward of a relatively perfect object along a flat proper
finitely presented morphism of algebraic spaces is perfect. -/
theorem pushforwardDerived_isPerfect_of_isPerfectRelativeTo
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Proper f] [Flat f] [FinitePresentation f]
    (E : ModuleDerived X) (hE : IsPerfectRelativeTo f E) :
    IsPerfect ((Modules.moduleDerivedPushforward f).obj E) := sorry

/-- The canonical derived base-change map for a relatively perfect object along
a flat proper finitely presented morphism of algebraic spaces is an isomorphism
for every cartesian base change. -/
theorem pushforwardDerived_baseChange_isIso_of_isPerfectRelativeTo
    {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [Proper f] [Flat f] [FinitePresentation f]
    (sq : IsPullback g' f' f g) (E : ModuleDerived X) (hE : IsPerfectRelativeTo f E) :
    IsIso ((DerivedBaseChange.map (derivedPullbackPushforwardAdjunction f)
        (derivedPullbackPushforwardAdjunction f')
        (DerivedQCoh.cohomologyBaseChangeCartesianIso sq)).app E) := sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
