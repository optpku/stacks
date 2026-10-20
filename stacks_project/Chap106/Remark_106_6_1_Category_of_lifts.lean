/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap106.Remark_106_6_1_Category_of_lifts_Category
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
@[stacks 0CJP] #check Lift.Object.Hom

/- Remark 106.6.1 (Category of lifts) (2): the systems `(U, U', a, i, x', α)`
with `a` étale, `x'` smooth, and `U = X ×_{X'} U'` are the objects of a
category `C` of lifts along a thickening `iX : X ⟶ X'` of a smooth map
`x : W.toGroupoids ⟶ X`. -/
@[stacks 0CJP] #check Lift.category

/- Remark 106.6.1 (Category of lifts) (3): the rule `p : C ⥤ W_spaces,étale`
sending a lift `(U, U', a, i, x', α)` to the étale map `a : U ⟶ W` is a
functor (see Properties of Spaces, Definition 66.18.2). -/
@[stacks 0CJP] #check Lift.p
