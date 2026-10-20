/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Cohomology
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Localization
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cohomology over a localized ringed site

The localization `X/U` has terminal object `Over.mk (𝟙 U)`.  This file owns the derived
cohomology comparison at that object; chapter files only recall the statement.
-/

@[expose] public section

open CategoryTheory Opposite

noncomputable section

universe z u v w

namespace RingedSite.Hom.ModuleDerived.Localization

variable (X : RingedSite.{u, v, w}) (U : X)
variable [UnivLE.{max u v, z}]

/-- The degree-`q` cohomology at the terminal object of the localized ringed site `X/U`. -/
@[stacks 0D6F "cohomology on the localization at an object"]
abbrev localizedCohomologyOverObject
    [IsGrothendieckAbelian (ModuleCat.{z} (X.localization U))]
    (K : ModuleDerived.{z} X) (q : ℤ) : AddCommGrpCat.{z} :=
  ModuleDerived.cohomologyOverObject (X.localization U) (Over.mk (𝟙 U))
    ((localizedRestrictionDerived X U).obj K) q

/-- Lemma 21.20.2 (0D6F): cohomology over `U` agrees with cohomology on the localized ringed
site `X/U` at its terminal object. -/
@[stacks 0D6F]
theorem cohomologyOverObject_isomorphic_localization
    [IsGrothendieckAbelian (ModuleCat.{z} X)]
    [IsGrothendieckAbelian (ModuleCat.{z} (X.localization U))]
    (K : ModuleDerived.{z} X) (q : ℤ) :
    IsIsomorphic
      (ModuleDerived.cohomologyOverObject X U K q)
      (localizedCohomologyOverObject X U K q) := sorry

end RingedSite.Hom.ModuleDerived.Localization
