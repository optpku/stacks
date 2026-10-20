/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap86.«86_7_0_1_Pullback»
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.Pushforward.RightAdjoint.ProjectionFormula
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Induced.Cochain

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open CategoryTheory.DerivedCategory CategoryTheory.MonoidalCategory ComplexShape ObjectProperty
open CategoryTheory.Pretriangulated CategoryTheory.Functor

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

variable {S : Scheme.{u}}

/-- The cochain-level counit `Lf^*(Q K) ⟶ Q(f^* K)` of derived module pullback. -/
noncomputable def modulePullbackDerived_cochainCounit
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (K : CochainComplex (Modules Y) ℤ) :
    (modulePullbackDerived f).obj (DerivedCategory.Q.obj K) ⟶
      DerivedCategory.Q.obj
        (((Modules.pullback f).mapHomologicalComplex (up ℤ)).obj K) :=
  (modulePullbackDerived f).map
      ((DerivedCategory.quotientCompQhIso (Modules Y)).inv.app K) ≫
    ((modulePullbackToDerived f).totalLeftDerivedCounit
        (DerivedCategory.Qh : HomotopyCategory (Modules Y) (up ℤ) ⥤ ModuleDerived Y)
        (ModuleQis Y)).app
      ((HomotopyCategory.quotient (Modules Y) (up ℤ)).obj K) ≫
    (Homotopy.cochainIso (Modules.pullback f)).hom.app K

#check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.pullbackTensorComparison :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (K L : DerivedQCoh Y),
    (pullback f).obj (tensorObj K L) ⟶
      tensorObj ((pullback f).obj K) ((pullback f).obj L))

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
