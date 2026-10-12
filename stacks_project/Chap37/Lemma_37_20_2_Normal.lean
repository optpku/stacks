/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Normal

@[expose] public section

open CategoryTheory

universe u

#check (AlgebraicGeometry.Normal :
  {X Y : AlgebraicGeometry.Scheme.{u}} → (X ⟶ Y) → Prop)
