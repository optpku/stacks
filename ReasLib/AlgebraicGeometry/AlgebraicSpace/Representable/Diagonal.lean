/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Representable

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.representableByAlgebraicSpaces

/-- A morphism of presheaves representable by algebraic spaces has a relative diagonal
representable by algebraic spaces. -/
theorem pullback_diagonal {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u} (a : F ⟶ G)
    [HasPullback a a] (ha : representableByAlgebraicSpaces a) :
    representableByAlgebraicSpaces (pullback.diagonal a) := sorry

end AlgebraicGeometry.AlgebraicSpace.representableByAlgebraicSpaces
