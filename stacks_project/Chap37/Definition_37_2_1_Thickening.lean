/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening

@[expose] public section

open CategoryTheory

universe u

#check (AlgebraicGeometry.IsThickening :
  {X Y : AlgebraicGeometry.Scheme.{u}} → (X ⟶ Y) → Prop)
