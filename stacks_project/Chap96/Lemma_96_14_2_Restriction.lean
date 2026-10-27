/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.SpaceComparison
public import stacks_project.Chap96.Definition_96_11_1_QCoh

/-! # Restriction to a representing small étale site -/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- Transport from fppf modules to modules on the associated étale ringed site. -/
abbrev toEtaleRingedModules (X : GroupoidsOver S) :
    RingedSite.ModuleCat.{u} (fppfRingedSite X) ⥤
      SheafOfModules.{u} (etaleRingedSite X).structureSheaf :=
  toEtaleModules X

#check (AlgebraicGeometry.GroupoidsOver.QCoh.restrict :
  ∀ {S : Scheme.{u}} {F : AlgebraicSpace S} {X : GroupoidsOver S}
    (e : F.toGroupoids ≌ X), QCoh X ⥤ AlgebraicSpace.QCoh F)

#check (AlgebraicGeometry.GroupoidsOver.QCoh.piStar :
  ∀ {S : Scheme.{u}} {F : AlgebraicSpace S} {X : GroupoidsOver S}
    (e : F.toGroupoids ≌ X), AlgebraicSpace.QCoh F ⥤ QCoh X)

end AlgebraicGeometry.GroupoidsOver
