/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Localization
public import ReasLib.AlgebraicGeometry.RingedSite.Localization
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Basic
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Restriction of modules to localized ringed sites

The restriction functor from a ringed site to its localization at an object is the
fixed-ring-sheaf restriction `SheafOfModules.Localization.restriction` of the structure sheaf,
spelled on bundled ringed sites.  Its additivity and exactness are the canonical instances of
that owner and are found by typeclass inference.  Complex- and derived-level restriction functors
are induced from it in their respective layers.
-/

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

namespace RingedSite.Hom

/-- Restriction of module sheaves from a ringed site to the ringed site localized at an object. -/
@[stacks 04IX "restriction of module sheaves"]
abbrev localizedRestriction.{z, u, v, w}
    (X : RingedSite.{u, v, w}) (U : X.carrier) :
    ModuleCat.{z} X ⥤ ModuleCat.{z} (X.localization U) :=
  SheafOfModules.Localization.restriction X.structureSheaf U

section

universe z u v w

/-- Restriction to a localized ringed site is additive. -/
@[deprecated "use the instance `SheafOfModules.pushforward_additive`" (since := "2026-10-15")]
theorem localizedRestriction_additive
    (X : RingedSite.{u, v, w}) (U : X.carrier) :
    (localizedRestriction.{z} X U).Additive := inferInstance

/-- Restriction to a localized ringed site preserves finite limits. -/
@[deprecated SheafOfModules.Localization.restriction_preservesFiniteLimits
  (since := "2026-10-15")]
theorem localizedRestriction_preservesFiniteLimits
    (X : RingedSite.{u, v, w}) (U : X.carrier) :
    PreservesFiniteLimits (localizedRestriction.{z} X U) := inferInstance

/-- Restriction to a localized ringed site preserves finite colimits. -/
@[deprecated SheafOfModules.Localization.restriction_preservesFiniteColimits
  (since := "2026-10-15")]
theorem localizedRestriction_preservesFiniteColimits
    (X : RingedSite.{u, v, w}) (U : X.carrier) :
    PreservesFiniteColimits (localizedRestriction.{z} X U) := inferInstance

end

end RingedSite.Hom
