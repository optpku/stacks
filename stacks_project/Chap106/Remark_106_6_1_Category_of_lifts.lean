/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Lift.Category
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicStack
open scoped Bicategory

universe u

/- Remark 106.6.1 (Category of lifts) (1): a morphism of lifts is a triple
`(f, f', γ)` with `f` a map of algebraic spaces over `W`, `f'` restricting to
`f`, and a right-triangle 2-cell `γ`, required to be compatible with the square
2-cells by `β = j*γ ∘ f*α`. The Lean Hom direction is `f : ξ.U ⟶ η.U`, matching
the displayed diagram 106.6.1.2, the existing unbundled Hom, and the étale site
of `W`, rather than the remark's swapped prose labels `(U, …) → (V, …)`. -/
@[stacks 0CJP] #check (AlgebraicGeometry.AlgebraicStack.Lift.Object.Hom :
  ∀ {S : Scheme.{u}} {X X' : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack X']
    {iX : X ⟶ X'} [IsThickening iX] {W : AlgebraicSpace S}
    {x : W.toGroupoids ⟶ X} [Groupoids.Hom.Smooth x],
    AlgebraicGeometry.AlgebraicStack.Lift.Object iX x →
      AlgebraicGeometry.AlgebraicStack.Lift.Object iX x → Type (u + 1))

/- Remark 106.6.1 (Category of lifts) (2): the systems `(U, U', a, i, x', α)`
with `a` étale, `x'` smooth, and `U = X ×_{X'} U'` are the objects of a
category `C` of lifts along a thickening `iX : X ⟶ X'` of a smooth map
`x : W.toGroupoids ⟶ X`. -/
@[stacks 0CJP] #check (AlgebraicGeometry.AlgebraicStack.Lift.category :
  ∀ {S : Scheme.{u}} {X X' : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack X']
    (iX : X ⟶ X') [IsThickening iX] {W : AlgebraicSpace S}
    (x : W.toGroupoids ⟶ X) [Groupoids.Hom.Smooth x],
    Category.{u + 1} (AlgebraicGeometry.AlgebraicStack.Lift.Object iX x))

/- Remark 106.6.1 (Category of lifts) (3): the rule `p : C ⥤ W_spaces,étale`
sending a lift `(U, U', a, i, x', α)` to the étale map `a : U ⟶ W` is a
functor (see Properties of Spaces, Definition 66.18.2). -/
@[stacks 0CJP] #check (AlgebraicGeometry.AlgebraicStack.Lift.p :
  ∀ {S : Scheme.{u}} {X X' : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack X']
    (iX : X ⟶ X') [IsThickening iX] {W : AlgebraicSpace S}
    (x : W.toGroupoids ⟶ X) [Groupoids.Hom.Smooth x],
    AlgebraicGeometry.AlgebraicStack.Lift.Object iX x ⥤ AlgebraicSpace.spacesEtaleSite W)
