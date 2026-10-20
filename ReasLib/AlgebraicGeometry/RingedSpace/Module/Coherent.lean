/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Site
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Coherent Sheaves of Modules

This file exposes the ringed-space view of the site-level
`SheafOfModules.IsCoherent` owner. On the open-set site, the generic definition already gives
the ringed-space notion, so no second coherence class or object property is needed.

## Main declarations

* `SheafOfModules.isCoherent` — coherence over an arbitrary ringed site as an `ObjectProperty`
* `AlgebraicGeometry.RingedSpace.Coh` — the full subcategory of coherent modules
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

variable {X : RingedSpace.{u}}


namespace AlgebraicGeometry.RingedSpace

/-- The full subcategory of coherent sheaves of modules on a ringed space. -/
@[stacks 01BV "coherent module category"]
abbrev Coh (X : RingedSpace.{u}) :=
  (SheafOfModules.isCoherent X.ringCatSheaf).FullSubcategory


end AlgebraicGeometry.RingedSpace
