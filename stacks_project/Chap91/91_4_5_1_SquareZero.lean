/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.SquareZeroExtension

/-!
# Trivial square-zero algebra sheaves on a ringed space

The geometric square-zero extension is provided by the reusable ringed-space
owner and remains available under its established names.
-/

universe u

open AlgebraicGeometry

#check (AlgebraicGeometry.RingedSpace.squareZeroSheaf :
  {X : RingedSpace.{u}} → X.Modules → TopCat.Sheaf CommRingCat.{u} X)

#check (AlgebraicGeometry.RingedSpace.SquareZeroSheaf.fst :
  {X : RingedSpace.{u}} → (M : X.Modules) →
    AlgebraicGeometry.RingedSpace.squareZeroSheaf M ⟶ X.sheaf)

#check (AlgebraicGeometry.RingedSpace.SquareZeroSheaf.inl :
  {X : RingedSpace.{u}} → (M : X.Modules) →
    X.sheaf ⟶ AlgebraicGeometry.RingedSpace.squareZeroSheaf M)
