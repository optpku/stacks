module

public import stacks_project.Chap101.«101_39_1_1_ValuativeSquare»
public import ReasLib.CategoryTheory.Bicategory.DottedArrow.Construction
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

variable {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
variable {f : X ⟶ Y} (sq : AlgebraicStack.ValuativeCommSq f)
variable (A A' : DottedArrow sq.toCone)

/- Definition 101.39.1 (1): given a morphism `f : X ⟶ Y` of algebraic stacks and a
solid 2-commutative valuative square `Spec(K) —x→ X` over `Spec(A) —y→ Y` with
vertical `j` and 2-cell `γ : j ≫ y ≅ x ≫ f`, a dotted arrow is a triple
`(a, α, β)` with `a : Spec(A) ⟶ X`, `α : j ≫ a ⟶ x`, `β : y ⟶ a ≫ f`, and
`γ = (id_f ⋆ α) ∘ (β ⋆ id_j)`. This is `DottedArrow sq.toCone`, with fields
`arrow`, `left`, `right` and triangle `comm` (Lean uses `≫`, `◁`/`▷`,
`whiskerLeftIso`, `whiskerRightIso`, and `≪≫`). -/
@[stacks 0CLA]
#check (DottedArrow sq.toCone)

/- Definition 101.39.1 (2): a morphism of dotted arrows `(a, α, β) ⟶ (a', α', β')`
is a 2-arrow `θ : a ⟶ a'` such that `α = α' ∘ (θ ⋆ id_j)` and
`β' = (id_f ⋆ θ) ∘ β`. This is `DottedArrow.Hom A A'`. -/
@[stacks 0CLA]
#check (DottedArrow.Hom A A')
