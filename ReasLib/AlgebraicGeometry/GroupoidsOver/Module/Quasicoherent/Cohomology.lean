/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent
public import ReasLib.AlgebraicGeometry.RingedSite.Module.UniverseLift
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-! # Cohomology of quasi-coherent modules on the fppf site -/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.QCoh

variable {S : Scheme.{u}}

/-- The cohomology group `H^n(X, F)` of a quasi-coherent module, computed as
fppf abelian sheaf cohomology of the carrier-lifted underlying module. -/
noncomputable abbrev cohomology (X : GroupoidsOver S) (F : QCoh X) (n : ℕ)
    [HasSheafify (ringedSite X).siteTopology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf (ringedSite X).siteTopology AddCommGrpCat.{u + 1})] :
    AddCommGrpCat.{u + 1} :=
  (Sheaf.functorH (ringedSite X).siteTopology n).obj
    ((SheafOfModules.toSheaf (ringedSite X).structureSheaf).obj
      (RingedSite.Module.carrierLift (ringedSite X) ((QCoh.inclusion X).obj F)))

/-- Quasi-coherent cohomology is fppf abelian sheaf cohomology of the
carrier-lifted underlying module. -/
theorem cohomology_eq (X : GroupoidsOver S) (F : QCoh X) (n : ℕ)
    [HasSheafify (ringedSite X).siteTopology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf (ringedSite X).siteTopology AddCommGrpCat.{u + 1})] :
    cohomology X F n =
      (Sheaf.functorH (ringedSite X).siteTopology n).obj
        ((SheafOfModules.toSheaf (ringedSite X).structureSheaf).obj
          (RingedSite.Module.carrierLift (ringedSite X)
            ((QCoh.inclusion X).obj F))) :=
  rfl

end AlgebraicGeometry.GroupoidsOver.QCoh
