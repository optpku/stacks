module

public import stacks_project.Chap97.Definition_97_8_1_Algebraic

/-!
# Diagonals of algebraic morphisms of stacks in groupoids

If a 1-morphism of stacks in groupoids over `(Sch/S)_fppf` is algebraic and the
target diagonal is representable by algebraic spaces, then the source diagonal
is representable by algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open AlgebraicGeometry.Groupoids.Hom
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry

/-- Lemma 97.8.4: Let `S` be a scheme. Let `F : X ⟶ Y` be a 1-morphism of
stacks in groupoids over `(Sch/S)_fppf`. If `F` is algebraic and
`Δ : Y ⟶ Y × Y` is representable by algebraic spaces, then
`Δ : X ⟶ X × X` is representable by algebraic spaces. -/
@[stacks 0D3R]
theorem relativelyRepresentableByAlgebraicSpaces.diagonal_of_algebraic
    {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) X.p]
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) Y.p]
    (F : X ⟶ Y) [Algebraic F]
    (hY : relativelyRepresentableByAlgebraicSpaces
      (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} Y)) :
    relativelyRepresentableByAlgebraicSpaces
      (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X) :=
  sorry

end AlgebraicGeometry
