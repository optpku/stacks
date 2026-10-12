/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.MultiplicativeGroup

open CategoryTheory
open AlgebraicGeometry

universe u

#check (AlgebraicGeometry.MultiplicativeGroup.groupScheme :
  CommGrp (Over (Spec (CommRingCat.of (ULift.{u} ℤ)))))
