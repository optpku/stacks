/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Cartesian

universe u

#check (AlgebraicGeometry.GroupoidScheme.CartesianOver :
  {S : AlgebraicGeometry.Scheme.{u}} →
    AlgebraicGeometry.GroupoidScheme S → CategoryTheory.Cat)
