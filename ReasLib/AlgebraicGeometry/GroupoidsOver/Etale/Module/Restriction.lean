/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pushforward
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.SmallEtaleComparison
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.DirectImage

/-!
# Restriction of étale modules to a representing algebraic space

Restriction through a representing equivalence is module pushforward from the
associated étale ringed site to the small étale ringed site of the space.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Functor Opposite
open FiberedCategoryOver.Groupoids
open RingedSite.Hom
open CategoryTheory.Limits
open CategoryTheory.Sheaf.InternalModule
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- Restriction of an étale sheaf of `𝒪_X`-modules to the small étale site of a
representing algebraic space `U`, as `F |_{U_étale} = π_{U,*} F`. -/
def restrictModules {U : AlgebraicSpace S} {X : GroupoidsOver S} (e : U.toGroupoids ≌ X) :
    SheafOfModules.{u} (etaleRingedSite X).structureSheaf ⥤
      SheafOfModules.{u} (AlgebraicSpace.structureSheaf U) :=
  (pi U X e).modulePushforward.{u}

/-- `restrictModules e` is module pushforward along `π_U`. -/
theorem restrictModules_eq {U : AlgebraicSpace S} {X : GroupoidsOver S}
    (e : U.toGroupoids ≌ X) :
    restrictModules e = (pi U X e).modulePushforward.{u} :=
  rfl

/-- Sections of a restricted module sheaf over `W` étale over `U` are the original
sections on `u(W)`, after restriction of scalars along the structure-sheaf map
of `π_U`. -/
theorem restrictModules_obj {U : AlgebraicSpace S} {X : GroupoidsOver S}
    (e : U.toGroupoids ≌ X)
    (F : SheafOfModules.{u} (etaleRingedSite X).structureSheaf)
    (W : AlgebraicSpace.smallEtaleSite U) :
    ((restrictModules e).obj F).val.obj (op W) =
      (ModuleCat.restrictScalars ((pi U X e).structureSheafMap.hom.app (op W)).hom).obj
        (F.val.obj (op ((smallEtaleFunctor U X e).obj W))) :=
  sorry

end AlgebraicGeometry.GroupoidsOver
