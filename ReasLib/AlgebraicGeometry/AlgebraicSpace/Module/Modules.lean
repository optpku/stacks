/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.StructureSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf

@[expose] public section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.SmallEtale

/-- Modules on an algebraic space are sheaves of modules over its small étale structure
sheaf. -/
abbrev Modules {S : Scheme.{u}} (X : AlgebraicSpace S) :=
  SheafOfModules.{u} (structureSheaf X)

end AlgebraicGeometry.AlgebraicSpace.SmallEtale
