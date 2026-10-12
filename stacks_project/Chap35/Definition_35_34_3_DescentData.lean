/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DescentData

open CategoryTheory

universe u v

#check (@AlgebraicGeometry.Scheme.DescentData :
  {I : Type v} → {S : AlgebraicGeometry.Scheme.{u}} →
    (X : I → AlgebraicGeometry.Scheme.{u}) →
      ((i : I) → X i ⟶ S) → Type (max (max v (u + 1)) u))
