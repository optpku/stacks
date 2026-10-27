/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.LocallyGiven

/-!
# Locally given derived modules on a ringed site

The ringed-site specialization of locally given derived modules and its restriction
comparisons are re-exported from the derived-module library.
-/

@[expose] public section

open CategoryTheory RingedSite RingedSite.Hom

universe u v w z

#check (RingedSite.ModuleDerived.restriction :
  ∀ {X : RingedSite.{u, v, w}} [UnivLE.{max u v, z}] {U V : X},
    (V ⟶ U) → ModuleCat.{z} (X.localization U) ⥤ ModuleCat.{z} (X.localization V))
