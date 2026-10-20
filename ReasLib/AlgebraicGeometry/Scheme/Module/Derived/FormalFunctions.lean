/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.CompletionMap
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pushforward
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.IdealSubobject.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Basic

@[expose] public section

open CategoryTheory SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived.DerivedCompletion

open RingedSite.Hom.ModuleDerived

variable {X S : Scheme.{u}}

/-- Derived pushforward carries completion along the pulled-back ideal to completion along the
original finite-type quasi-coherent ideal. -/
theorem pushforwardSingle (f : X ⟶ S) (I : S.IdealSheafData) [I.toModule.IsQuasicoherent]
    (hI : I.IsFiniteType) (F : X.Modules) [F.IsQuasicoherent]
    {Khat : DerivedCategory X.Modules}
    (η : (DerivedCategory.singleFunctor X.Modules 0).obj F ⟶ Khat)
    (hη : IsDerivedCompletion.{u, u, u, u} (I.comap f).toSubobject η) :
    IsDerivedCompletion.{u, u, u, u} I.toSubobject
      ((RingedSpace.moduleDerivedPushforward f.toShHom).map η) := sorry

end AlgebraicGeometry.Scheme.ModuleDerived.DerivedCompletion
