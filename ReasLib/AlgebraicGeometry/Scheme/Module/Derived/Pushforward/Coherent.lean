/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Cohomology.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pushforward
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pushforward.BoundedBelow
public import ReasLib.AlgebraicGeometry.Scheme.Module.Support.Proper
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Bounded

@[expose] public section

open CategoryTheory
open DerivedCategory.TStructure

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived

/-- Derived pushforward along a locally finite type morphism to a Noetherian scheme preserves
bounded coherent cohomology when every cohomology sheaf has proper support over the base. -/
theorem pushforwardBoundedCoherentOfProperSupport
    {X S : Scheme.{u}} (f : X ⟶ S) [IsNoetherian S] [LocallyOfFiniteType f]
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hE_coherent : DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) E)
    (hE_bounded : (t.bounded : ObjectProperty
      (RingedSpace.ModuleDerived X.toRingedSpace)) E)
    [∀ i : ℤ, Scheme.Modules.HasProperSupportOver f
      (RingedSpace.ModuleDerived.cohomologySheaf E i)] :
    DerivedCategory.cohomologyIn
        (SheafOfModules.isCoherent S.toRingedSpace.ringCatSheaf)
        ((RingedSpace.moduleDerivedPushforward f.toShHom).obj E) ∧
      (t.bounded : ObjectProperty (RingedSpace.ModuleDerived S.toRingedSpace))
        ((RingedSpace.moduleDerivedPushforward f.toShHom).obj E) := sorry

/-- Bounded-below derived pushforward along a locally finite type morphism to a Noetherian
scheme has coherent cohomology when every cohomology sheaf has proper support over the base. -/
theorem pushforwardBoundedBelowCoherentOfProperSupport
    {X S : Scheme.{u}} (f : X ⟶ S) [IsNoetherian S] [LocallyOfFiniteType f]
    (E : DerivedCategory.Plus.CohomologyIn
      (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf))
    [∀ i : ℤ, Scheme.Modules.HasProperSupportOver f
      ((DerivedCategory.Plus.homologyFunctor X.toRingedSpace.Modules i).obj E.obj)] :
    DerivedCategory.Plus.cohomologyIn
      (SheafOfModules.isCoherent S.toRingedSpace.ringCatSheaf)
      ((RingedSpace.moduleDerivedPushforwardPlus f.toShHom).obj E.obj) := sorry

end AlgebraicGeometry.Scheme.ModuleDerived
