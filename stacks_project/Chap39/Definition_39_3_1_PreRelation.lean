/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.PreRelation

universe u

variable {S : AlgebraicGeometry.Scheme.{u}} (U : CategoryTheory.Over S)

#check (AlgebraicGeometry.Scheme.PreRelation U : Type (u + 1))
