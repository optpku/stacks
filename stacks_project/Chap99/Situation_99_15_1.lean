/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap99.Situation_99_15_1_Category

/-!
# The stack of curves

Situation 99.15.1 introduces the category of families of curves: morphisms of
algebraic spaces to schemes that are flat, proper, of finite presentation, and
of relative dimension at most `1`, with cartesian morphisms, viewed over
`Sch_fppf`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace.Spaces.Curves (Obj p base)

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces

/-- Situation 99.15.1: the category Curves of families of curves. An object is
a morphism `f : X ⟶ S` where the base `S` is a scheme, the total space `X` is
an algebraic space, and `f` is flat, proper, of finite presentation, and of
relative dimension at most `1`. A morphism `(X' ⟶ S') ⟶ (X ⟶ S)` is a pair
`(f, g)` with `f : X' ⟶ X` a morphism of algebraic spaces and `g : S' ⟶ S` a
morphism of schemes forming a cartesian square, equivalently inducing an
isomorphism `X' ≅ S' ×_S X`. The forgetful functor `p : Curves ⥤ Sch_fppf`,
`(X ⟶ S) ↦ S`, presents Curves as a category over `Sch_fppf`, with `Over S`
playing the role of `Sch_fppf`. -/
@[stacks 0D4Z]
abbrev Curves := Obj

/-- The forgetful functor of Curves sends each family of curves to its base
scheme over `S`. -/
theorem Curves.forget_obj {S : Scheme.{u}} (P : Curves S) : (p S).obj P = base P :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Spaces
