module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import stacks_project.Chap76.Definition_76_9_1_FiniteOrder
public import stacks_project.Chap76.Lemma_76_52_4_Relative

/-!
# Relative perfectness along finite-order thickenings of algebraic spaces

In a cartesian square of algebraic spaces over a scheme, if `X' ⟶ Y'` is flat
and locally of finite presentation and `Y ⟶ Y'` is a finite-order thickening,
then `Y`-perfectness of `Li^* E'` implies `Y'`-perfectness of `E'`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.ModuleDerived

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsFiniteOrderThickening

/-- Lemma 76.54.4: Let `S` be a scheme. Consider a cartesian square of algebraic
spaces over `S` with morphisms `i : X ⟶ X'`, `f : X ⟶ Y`, `f' : X' ⟶ Y'`, and
`j : Y ⟶ Y'`, witnessed by `IsPullback i f f' j`. Assume `f'` is flat and
locally of finite presentation and `j` is a finite-order thickening. Let `E'`
be an object of `D(𝒪_{X'})`. If `E = Li^* E' = (pullback i).obj E'` is
`Y`-perfect, then `E'` is `Y'`-perfect. -/
@[stacks 0DL4]
theorem isPerfectRelativeTo_of_pullback {S : Scheme.{u}}
    {X X' Y Y' : AlgebraicSpace S} (i : X ⟶ X') (f : X ⟶ Y) (f' : X' ⟶ Y')
    (j : Y ⟶ Y') (sq : IsPullback i f f' j) [Flat f']
    [LocallyOfFinitePresentation f'] [IsFiniteOrderThickening j] [Flat f]
    [LocallyOfFinitePresentation f] (E' : ModuleDerived X')
    (hE : IsPerfectRelativeTo f ((pullback i).obj E')) :
    IsPerfectRelativeTo f' E' :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsFiniteOrderThickening
