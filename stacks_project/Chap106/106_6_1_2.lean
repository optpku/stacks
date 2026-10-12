/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap106.«106_6_1_2_Hom»
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicStack
open scoped Bicategory

universe u

/- 106.6.1.2: a morphism of lifts `(f, f', γ)` from `(V, V', b, j, y')` to
`(U, U', a, i, x')` over `W`, displayed as the 2-commutative diagram with
space maps `f : V ⟶ U` over `W` (so `f ≫ a = b`), `f' : V' ⟶ U'` restricting
to `f` (so `j ≫ f' = f ≫ i`), and 2-cell `γ : toGroupoids.map f' ≫ x' ≅ y'`
in the right triangle. -/
@[stacks 0CJR] #check Lift.Hom
#check Lift.Hom.mk
#check Lift.Hom.spec
