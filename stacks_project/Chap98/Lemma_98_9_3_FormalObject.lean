module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.FormalObject.Basic

/-! # Complete local algebras and formal objects

The complete local bases and their formal stage systems are re-exported here.
-/

@[expose] public section

universe u

variable {S : AlgebraicGeometry.Scheme.{u}}

#check (AlgebraicGeometry.CompleteLocalSAlgebra : AlgebraicGeometry.Scheme.{u} → Type (u + 1))

variable [AlgebraicGeometry.IsLocallyNoetherian S]

#check (AlgebraicGeometry.GroupoidsOver.FormalObject :
  AlgebraicGeometry.GroupoidsOver S → Type (u + 1))
