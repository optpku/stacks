/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Coherent.Category
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubset.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.TorDimension.Relative
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Support.Closed
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation

/-! # Perfect derived pushforward under finite relative Tor dimension -/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open DerivedCategory.TStructure

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- Along a locally of finite type quasi-separated morphism with Noetherian target, the derived
pushforward of a bounded coherent complex with degreewise proper support and finite relative
Tor dimension is perfect. -/
theorem pushforwardDerived_isPerfect_of_finiteTorDimension
    (f : X ⟶ Y)
    [LocallyOfFiniteType f] [QuasiSeparated f] [IsNoetherian Y]
    (E : ModuleDerived X)
    (hE_coherent : DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent (structureSheaf X)) E)
    (hE_bounded : (t.bounded : ObjectProperty (ModuleDerived X)) E)
    (hE_support : ∀ i : ℤ, ClosedSubset.ProperOver f
      (Modules.closedSupport
        ((DerivedCategory.homologyFunctor (Modules X) i).obj E)))
    (hE_tor : HasFiniteTorDimensionOver f E) :
    IsPerfect ((Modules.moduleDerivedPushforward f).obj E) := sorry

/-- Along a locally of finite type quasi-separated morphism with Noetherian target, the derived
pushforward of a bounded coherent complex with degreewise proper support and a fixed relative
Tor-amplitude interval is perfect. -/
theorem pushforwardDerived_isPerfect_of_hasTorAmplitudeInOver
    (f : X ⟶ Y)
    [LocallyOfFiniteType f] [QuasiSeparated f] [IsNoetherian Y]
    (E : ModuleDerived X)
    (hE_coherent : DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent (structureSheaf X)) E)
    (hE_bounded : (t.bounded : ObjectProperty (ModuleDerived X)) E)
    (hE_support : ∀ i : ℤ, ClosedSubset.ProperOver f
      (Modules.closedSupport
        ((DerivedCategory.homologyFunctor (Modules X) i).obj E)))
    (a b : ℤ) (hE_tor : HasTorAmplitudeInOver f E a b) :
    IsPerfect ((Modules.moduleDerivedPushforward f).obj E) := by
  exact pushforwardDerived_isPerfect_of_finiteTorDimension f E hE_coherent hE_bounded hE_support
    ((hasFiniteTorDimensionOver_iff f E).2 ⟨a, b, hE_tor⟩)

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
