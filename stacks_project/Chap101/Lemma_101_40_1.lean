module

public import ReasLib.CategoryTheory.Bicategory.DottedArrow.Groupoid
public import stacks_project.Chap101.«101_39_1_1_ValuativeSquare»
public import stacks_project.Chap101.Definition_101_4_1_Separation

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 101.40.1: If `f : X ⟶ Y` is a morphism of algebraic stacks, `Δ_f` is
quasi-separated, and for every valuative solid square (101.39.1.1) with every
choice of 2-cell `γ` as in Definition 101.39.1 the category of dotted arrows
is a setoid, then `Δ_f` is separated. -/
@[stacks 0CLR]
theorem diagonal_separated_of_quasiSeparated_of_dottedArrow_isThin
    {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (h_quasiSeparated :
      Groupoids.Hom.has (@AlgebraicSpace.QuasiSeparated S)
        (Hom.diagonal.{u + 1, u, u + 1} f))
    (h_isThin : ∀ sq : ValuativeCommSq f, Quiver.IsThin (DottedArrow sq.toCone)) :
    Groupoids.Hom.has (@AlgebraicSpace.Separated S)
      (Hom.diagonal.{u + 1, u, u + 1} f) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
