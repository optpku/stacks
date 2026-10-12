/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.ResolutionProperty
import StacksCheckRecall

universe u

/- Definition 36.36.1: a scheme has the resolution property when every finite-type
quasi-coherent module is the quotient of a finite locally free module. -/
@[stacks 0F86] #check (AlgebraicGeometry.Scheme.HasResolutionProperty :
  AlgebraicGeometry.Scheme.{u} → Prop)
