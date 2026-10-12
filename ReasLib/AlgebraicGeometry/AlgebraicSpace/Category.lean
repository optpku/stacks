/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints
public import Mathlib.CategoryTheory.InducedCategory

@[expose] public section

open CategoryTheory AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The category of algebraic spaces over `S`, induced by their functors of points. -/
abbrev Cat (S : Scheme.{u}) :=
  InducedCategory ((Over S)ᵒᵖ ⥤ Type u) (fun X : AlgebraicSpace S => X.functorOfPoints)

end AlgebraicGeometry.AlgebraicSpace
