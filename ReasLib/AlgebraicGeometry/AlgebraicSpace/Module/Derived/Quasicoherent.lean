/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Sheafification
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.SmallEtale

/-- Sheaves of modules on the small étale site carry their standard derived category. -/
instance modulesHasDerivedCategory {S : Scheme.{u}} (X : AlgebraicSpace S) :
    HasDerivedCategory (Modules X) :=
  HasDerivedCategory.standard (Modules X)

/-- The unbounded derived category of modules over the small étale structure sheaf. -/
abbrev ModuleDerived {S : Scheme.{u}} (X : AlgebraicSpace S) :=
  DerivedCategory (Modules X)

/-- The full subcategory of derived modules whose cohomology sheaves are
quasicoherent in every degree. -/
abbrev DerivedQCoh {S : Scheme.{u}} (X : AlgebraicSpace S) :=
  DerivedCategory.CohomologyIn (SheafOfModules.isQuasicoherent (structureSheaf X))

end AlgebraicGeometry.AlgebraicSpace.SmallEtale
