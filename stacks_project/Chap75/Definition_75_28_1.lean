/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ResolutionProperty
public import stacks_project.Chap75.Definition_75_28_1_ResolutionProperty
import StacksCheckRecall

universe u

variable {S : AlgebraicGeometry.Scheme.{u}}
variable (X : AlgebraicGeometry.AlgebraicSpace S)

/- Definition 75.28.1: an algebraic space over a scheme has the resolution property when
every finite-type quasi-coherent module is the quotient of a finite locally free module. -/
@[stacks 0GUS] #check
  (SheafOfModules.HasResolutionProperty
    (AlgebraicGeometry.AlgebraicSpace.structureSheaf X) : Prop)
