/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.Additive
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Localization
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Restriction of complexes to localized ringed sites

The complex-level restriction functor is obtained functorially from ordinary restriction of
module sheaves.  It is kept below the derived layer for use by strict-perfect and local-model
APIs.
-/

open CategoryTheory
open ComplexShape

noncomputable section

namespace RingedSite.Hom

/-- The functor on cochain complexes induced by restricting module sheaves to a localized
ringed site. -/
@[stacks 04IX "restriction of complexes of module sheaves"]
abbrev localizedRestrictionComplex.{z, u, v, w}
    (X : RingedSite.{u, v, w}) (U : X.carrier) :
    CochainComplex (ModuleCat.{z} X) ℤ ⥤
      CochainComplex (ModuleCat.{z} (X.localization U)) ℤ :=
  (localizedRestriction.{z} X U).mapHomologicalComplex (up ℤ)

end RingedSite.Hom
