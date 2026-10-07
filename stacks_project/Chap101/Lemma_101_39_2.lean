module

public import ReasLib.CategoryTheory.Bicategory.DottedArrow.Groupoid
public import stacks_project.Chap101.«101_39_1_1_ValuativeSquare»
public import stacks_project.Chap101.Definition_101_4_1_Separation
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

section

variable {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
variable {f : X ⟶ Y} (sq : AlgebraicStack.ValuativeCommSq f)

/- Lemma 101.39.2 (1): In the situation of Definition 101.39.1, the category of
dotted arrows is a groupoid. This is `DottedArrow.categoryIsGroupoid` on
`DottedArrow sq.toCone`, using that `GroupoidsOver S` is locally groupoidal. -/
@[stacks 0CLC]
#check (DottedArrow.categoryIsGroupoid sq.toCone : IsGroupoid (DottedArrow sq.toCone))

end

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 101.39.2 (2): In the situation of Definition 101.39.1, if the first
diagonal `Δ_f = Hom.diagonal f` is separated, then the category of dotted
arrows is a setoid, i.e. a thin groupoid. -/
@[stacks 0CLC]
theorem dottedArrow_isThin_of_diagonal_separated
    {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (h_diagonal :
      Groupoids.Hom.has (@AlgebraicSpace.Separated S)
        (Hom.diagonal.{u + 1, u, u + 1} f))
    (sq : ValuativeCommSq f) :
    Quiver.IsThin (DottedArrow sq.toCone) :=
  sorry

/-- Hom-spaces in the dotted-arrow category of a valuative square are
subsingleton when the first diagonal of `f` is separated. -/
theorem dottedArrow_subsingleton_hom_of_diagonal_separated
    {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (h_diagonal :
      Groupoids.Hom.has (@AlgebraicSpace.Separated S)
        (Hom.diagonal.{u + 1, u, u + 1} f))
    (sq : ValuativeCommSq f) (A A' : DottedArrow sq.toCone) :
    Subsingleton (A ⟶ A') :=
  sorry

/-- Automorphism groups of dotted arrows of a valuative square are
subsingleton when the first diagonal of `f` is separated. -/
theorem dottedArrow_subsingleton_aut_of_diagonal_separated
    {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (h_diagonal :
      Groupoids.Hom.has (@AlgebraicSpace.Separated S)
        (Hom.diagonal.{u + 1, u, u + 1} f))
    (sq : ValuativeCommSq f) (A : DottedArrow sq.toCone) :
    Subsingleton (Aut A) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
