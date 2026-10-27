/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.FiberwiseSerre

/-!
# Fiberwise weak Serre subcategories with bounded cohomology

The shared family owner supplies the fiberwise hypotheses and global membership predicate.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open RingedSite RingedSite.Localization

universe wι u v w

variable {X : RingedSite.{u, v, w}}
variable [UnivLE.{max u v, w}]
variable [X.siteTopology.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ U : X, (X.siteTopology.over U).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ {U V : X} (f : V ⟶ U),
    (SheafOfModules.restrictScalars.{w} (relocalization X f).structureMap).IsRightAdjoint]

variable (A : FiberwiseSerre.{wι, u, v, w} X)

/- Fiberwise weak Serre families determine the subcategory of modules whose restriction
to every slice belongs to the corresponding fiber subcategory. -/
#check (RingedSite.FiberwiseSerre.global A : ObjectProperty (ModuleCat.{w} X))
