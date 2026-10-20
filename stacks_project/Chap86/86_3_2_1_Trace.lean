/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.Pushforward.SheafyTrace

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
open CategoryTheory CategoryTheory.MonoidalClosed
open CategoryTheory.Functor.LaxMonoidal

universe u

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
variable [QuasiCompact f] [QuasiSeparated f]
variable [MonoidalCategory (ModuleDerived X)] [MonoidalCategory (ModuleDerived Y)]
variable [MonoidalClosed (ModuleDerived X)] [MonoidalClosed (ModuleDerived Y)]
variable [Functor.LaxMonoidal (moduleDerivedPushforward f)]
variable (a : DerivedQCoh Y ⥤ DerivedQCoh X) (adj : pushforwardCohomologyIn f ⊣ a)
variable (L : DerivedQCoh X) (K : DerivedQCoh Y)

#check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.sheafyTrace f a adj L K :
  (moduleDerivedPushforward f).obj ((ihom L.obj).obj (a.obj K).obj) ⟶
    (ihom ((moduleDerivedPushforward f).obj L.obj)).obj K.obj)

#check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.sheafyTrace_eq f a adj L K :
  sheafyTrace f a adj L K =
    InternalHom.comparison (moduleDerivedPushforward f) L.obj (a.obj K).obj ≫
      (ihom ((moduleDerivedPushforward f).obj L.obj)).map
        ((pushforwardCohomologyIn.inclusionIso f).inv.app (a.obj K) ≫
          (inclusion Y).map (adj.counit.app K)))
