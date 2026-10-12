/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous.Additive
public import ReasLib.AlgebraicGeometry.RingedSite.Localization
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Basic
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Restriction of modules to localized ringed sites

This file owns the ordinary restriction functor from a ringed site to its localization at an
object.  Complex- and derived-level restriction functors are induced from this owner in their
respective layers.
-/

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

namespace RingedSite.Hom

/-- Restriction of module sheaves from a ringed site to the ringed site localized at an object. -/
@[stacks 04IX "restriction of module sheaves"]
abbrev localizedRestriction.{z, u, v, w}
    (X : RingedSite.{u, v, w}) (U : X) :
    ModuleCat.{z} X ⥤ ModuleCat.{z} (X.localization U) :=
  (_root_.SheafOfModules.pushforward.{z} (𝟙 (X.structureSheaf.over U)) :
    ModuleCat.{z} X ⥤ ModuleCat.{z} (X.localization U))

section

universe z u v w

/-- Restriction to a localized ringed site is additive. -/
@[stacks 04IX "additivity of module restriction"]
theorem localizedRestriction_additive
    (X : RingedSite.{u, v, w}) (U : X) :
    (localizedRestriction.{z} X U).Additive := sorry

/-- Restriction to a localized ringed site preserves finite limits. -/
@[stacks 04IX "finite-limit preservation for module restriction"]
theorem localizedRestriction_preservesFiniteLimits
    (X : RingedSite.{u, v, w}) (U : X) :
    PreservesFiniteLimits (localizedRestriction.{z} X U) := sorry

/-- Restriction to a localized ringed site preserves finite colimits. -/
@[stacks 04IX "finite-colimit preservation for module restriction"]
theorem localizedRestriction_preservesFiniteColimits
    (X : RingedSite.{u, v, w}) (U : X) :
    PreservesFiniteColimits (localizedRestriction.{z} X U) := sorry

end

end RingedSite.Hom
