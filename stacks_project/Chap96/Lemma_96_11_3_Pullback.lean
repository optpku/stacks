/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.ObjectPullback

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

#check (AlgebraicGeometry.GroupoidsOver.structureSheafToPushforward :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S),
    (GroupoidsOver.structureSheaf X).obj ≅
      (X.p.op ⋙ ((Over.forget S).op ⋙ Scheme.Γ)) ⋙
        forget₂ CommRingCat.{u} RingCat.{u})

#check (AlgebraicGeometry.GroupoidsOver.objectPullback :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) (x : X.total),
    SheafOfModules.{u} (GroupoidsOver.structureSheaf X) ⥤
      RingedSite.ModuleCat.{u} (GroupoidsOver.objectPullbackSite X x))
