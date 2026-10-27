/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.PseudoCoherent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.CohomologyBaseChange.Pushforward

/-! # Derived pushforward of pseudo-coherent modules on algebraic spaces -/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived.PseudoCoherent

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- Derived pushforward along a flat proper morphism of finite presentation of
algebraic spaces preserves pseudo-coherent derived modules. -/
theorem pushforward
    (f : X ⟶ Y) [Proper f] [Flat f] [FinitePresentation f]
    (E : ModuleDerived X) (hE : IsPseudoCoherent X E) :
    IsPseudoCoherent Y ((Modules.moduleDerivedPushforward f).obj E) := sorry

/-- For a flat proper morphism of finite presentation of algebraic spaces, the
canonical derived base-change map at a pseudo-coherent derived module is an
isomorphism for every cartesian square. -/
theorem baseChange_isIso
    {X' Y' : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [Proper f] [Flat f] [FinitePresentation f]
    (sq : IsPullback g' f' f g) (E : ModuleDerived X) (hE : IsPseudoCoherent X E) :
    IsIso ((DerivedBaseChange.map (derivedPullbackPushforwardAdjunction f)
        (derivedPullbackPushforwardAdjunction f')
        (DerivedQCoh.cohomologyBaseChangeCartesianIso sq)).app E) := sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived.PseudoCoherent
