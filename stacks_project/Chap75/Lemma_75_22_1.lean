/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap75.Lemma_75_20_7_BaseChange

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Perfect.Pushforward.FiniteTorDimension
import StacksCheckRecall

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open DerivedCategory.TStructure

universe u

#check (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.HasFiniteTorDimensionOver :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y), ModuleDerived X → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.hasFiniteTorDimensionOver_iff :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (E : ModuleDerived X),
    AlgebraicGeometry.AlgebraicSpace.ModuleDerived.HasFiniteTorDimensionOver f E ↔
      ∃ a b : ℤ, AlgebraicGeometry.AlgebraicSpace.ModuleDerived.HasTorAmplitudeInOver f E a b)

/- Lemma 75.22.1: derived pushforward of a bounded coherent complex with degreewise
proper support and finite Tor dimension over inverse-image coefficients is perfect. -/
@[stacks 08IS] #check (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.pushforwardDerived_isPerfect_of_finiteTorDimension :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [QuasiSeparated f] [IsNoetherian Y]
    (E : ModuleDerived X)
    (hE_coherent : DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent (structureSheaf X)) E)
    (hE_bounded : (t.bounded : ObjectProperty (ModuleDerived X)) E)
    (hE_support : ∀ i : ℤ, ClosedSubset.ProperOver f
      (Modules.closedSupport
        ((DerivedCategory.homologyFunctor (Modules X) i).obj E)))
    (hE_tor : AlgebraicGeometry.AlgebraicSpace.ModuleDerived.HasFiniteTorDimensionOver f E),
    AlgebraicGeometry.AlgebraicSpace.ModuleDerived.IsPerfect ((Modules.moduleDerivedPushforward f).obj E))

#check (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.pushforwardDerived_isPerfect_of_hasTorAmplitudeInOver :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [QuasiSeparated f] [IsNoetherian Y]
    (E : ModuleDerived X)
    (hE_coherent : DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent (structureSheaf X)) E)
    (hE_bounded : (t.bounded : ObjectProperty (ModuleDerived X)) E)
    (hE_support : ∀ i : ℤ, ClosedSubset.ProperOver f
      (Modules.closedSupport
        ((DerivedCategory.homologyFunctor (Modules X) i).obj E)))
    (a b : ℤ) (hE_tor : AlgebraicGeometry.AlgebraicSpace.ModuleDerived.HasTorAmplitudeInOver f E a b),
    AlgebraicGeometry.AlgebraicSpace.ModuleDerived.IsPerfect ((Modules.moduleDerivedPushforward f).obj E))
