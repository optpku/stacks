/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.Module.Restriction

/-! # Restriction of étale modules to a representing algebraic space -/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite
open AlgebraicGeometry.GroupoidsOver
open FiberedCategoryOver.Groupoids
open RingedSite.Hom
open scoped Bicategory

universe u

#check (AlgebraicGeometry.GroupoidsOver.restrictModules :
  ∀ {S : Scheme.{u}} {U : AlgebraicSpace S} {X : GroupoidsOver S} (e : U.toGroupoids ≌ X),
    SheafOfModules.{u} (etaleRingedSite X).structureSheaf ⥤
      SheafOfModules.{u} (AlgebraicSpace.structureSheaf U))

#check (AlgebraicGeometry.GroupoidsOver.restrictModules_eq :
  ∀ {S : Scheme.{u}} {U : AlgebraicSpace S} {X : GroupoidsOver S}
    (e : U.toGroupoids ≌ X),
    restrictModules e = (pi U X e).modulePushforward.{u})

#check (AlgebraicGeometry.GroupoidsOver.restrictModules_obj :
  ∀ {S : Scheme.{u}} {U : AlgebraicSpace S} {X : GroupoidsOver S}
    (e : U.toGroupoids ≌ X)
    (F : SheafOfModules.{u} (etaleRingedSite X).structureSheaf)
    (W : AlgebraicSpace.smallEtaleSite U),
    ((restrictModules e).obj F).val.obj (op W) =
      (ModuleCat.restrictScalars ((pi U X e).structureSheafMap.hom.app (op W)).hom).obj
        (F.val.obj (op ((smallEtaleFunctor U X e).obj W))))
