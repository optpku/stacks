/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ResolutionProperty
public import stacks_project.Chap66.Definition_66_29_1_RingedSite

/-!
# The resolution property for algebraic spaces

The resolution property expresses the existence of finite locally free epimorphic
presentations of finite-type quasi-coherent modules on an algebraic space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An algebraic space has the resolution property when its structure sheaf has the generic
resolution property for sheaves of modules. -/
abbrev HasResolutionProperty {S : Scheme.{u}} (X : AlgebraicSpace S) : Prop :=
  SheafOfModules.HasResolutionProperty (structureSheaf X)

end AlgebraicGeometry.AlgebraicSpace
