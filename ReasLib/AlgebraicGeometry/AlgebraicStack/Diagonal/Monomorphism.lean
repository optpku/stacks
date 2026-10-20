module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Monomorphism

/-!
# Monomorphisms among diagonals of algebraic stacks

A morphism of algebraic stacks is representable by algebraic spaces if and
only if its first diagonal is a monomorphism. Its second diagonal is always
a monomorphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Groupoids.Hom
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- A morphism of algebraic stacks is representable by algebraic spaces if
and only if its first diagonal is a monomorphism. -/
theorem relativelyRepresentableByAlgebraicSpaces_iff_mono_diagonal
    {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack Y] (f : X ⟶ Y) :
    relativelyRepresentableByAlgebraicSpaces f ↔
      Groupoids.Hom.Mono (Hom.diagonal.{u + 1, u, u + 1} f) :=
  sorry

end AlgebraicGeometry.AlgebraicStack

namespace AlgebraicGeometry.Groupoids.Hom
namespace Mono

/-- The second diagonal of a morphism of algebraic stacks is a monomorphism. -/
instance secondDiagonal {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y} :
    Mono (Hom.diagonal.{u + 1, u, u + 1}
      (Hom.diagonal.{u + 1, u, u + 1} f)) :=
  sorry

end Mono
end AlgebraicGeometry.Groupoids.Hom
