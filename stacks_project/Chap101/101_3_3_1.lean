module

public import stacks_project.Chap101.«101_3_3_1_Isom»
public import stacks_project.Chap101.«101_3_3_1_Pullback»
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
import Mathlib.Tactic.CrossRefAttribute

/-!
# Equation 101.3.3.1 — fibre square of Isom sheaves along a diagonal

For a morphism of algebraic stacks, the 2-fibre product of the diagonal
against a 2-Yoneda triple `(x, x', α)` is cartesian as a square of sheaves
over `T`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open FiberedCategoryOver.Groupoids
open CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal
open CategoryTheory.Limits
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- 101.3.3.1: Let `f : X ⟶ Y` be a morphism of algebraic stacks over `S`, let
`T` be a scheme over `S`, and let `a : T ⟶ X ×_Y X` be given by the 2-Yoneda
triple `(x, x', α)` with `x, x'` objects of `X` over `T` and
`α : f(x) ⟶ f(x')` in the fibre of `Y` over `T`. Then the square of sheaves
over `T` with corners `X ×_{X ×_Y X, a} T`, `Isom_X(x, x')`, `T`, and
`Isom_Y(f(x), f(x'))` is a fibre square. -/
@[stacks 04XT]
theorem isomSquare_isPullback {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {T : Over S}
    (x x' : X.p.Fiber T)
    (α : (fiberFunctor f T).obj x ≅ (fiberFunctor f T).obj x') :
    IsPullback (toIsom f x x' α) (toBase f x x' α)
      (isomMap f x x') (alphaSection f x x' α) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
