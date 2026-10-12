/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme

universe u

#check (AlgebraicGeometry.GroupoidScheme :
  (S : AlgebraicGeometry.Scheme.{u}) → Type (u + 1))

#check (AlgebraicGeometry.GroupoidScheme.Hom :
  {S : AlgebraicGeometry.Scheme.{u}} →
    AlgebraicGeometry.GroupoidScheme S → AlgebraicGeometry.GroupoidScheme S → Type u)
