/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints

/-!
# Morphisms of algebraic spaces

A morphism of algebraic spaces over a scheme `S` is a morphism of their functors of points.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism of algebraic spaces over a scheme `S` is a morphism of their functors of
points. -/
abbrev Hom {S : Scheme.{u}} (F F' : AlgebraicSpace S) :=
  F.functorOfPoints ⟶ F'.functorOfPoints

end AlgebraicGeometry.AlgebraicSpace
