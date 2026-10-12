/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit
public import stacks_project.Chap100.Definition_100_4_2_Points
public import stacks_project.Chap101.Lemma_101_45_5_Comparison
public import stacks_project.Chap101.Remark_101_19_5_AutomorphismGroup

/-!
# Base change of stabilizer-preserving morphisms

On a cartesian square of algebraic stacks, inducing an isomorphism of
automorphism groups is stable under base change, both at a point of `|X|` and
for the global comparison `I_X ⟶ X ×_Y I_Y`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.automorphismGroup

/-- Lemma 101.45.5 (1): let `c` be a cartesian diagram of algebraic stacks, and
let `x' ∈ |c.pt|` with image `Points.map c.fst x'` in `|X|`. If `f` induces an
isomorphism between automorphism groups at that image (Remark 101.19.5), then
`c.snd` induces an isomorphism between automorphism groups at `x'`. -/
@[stacks 0DUB]
theorem IsIsoAt.of_isBilimit {S : Scheme.{u}} {X Y Y' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Y']
    {f : X ⟶ Y} {g : Y' ⟶ Y} (c : PseudoPullbackCone f g)
    [AlgebraicStack c.pt] (hc : c.IsBilimit) (x' : |c.pt|)
    (hx : IsIsoAt f (Points.map c.fst x')) : IsIsoAt c.snd x' :=
  sorry

end AlgebraicGeometry.AlgebraicStack.automorphismGroup

namespace AlgebraicGeometry.AlgebraicStack.Inertia

/-- Lemma 101.45.5 (2): let `c` be a cartesian diagram of algebraic stacks. If
`comparison f : I_X ⟶ X ×_Y I_Y` is an isomorphism, then
`comparison c.snd : I_{c.pt} ⟶ c.pt ×_{Y'} I_{Y'}` is an isomorphism. -/
@[stacks 0DUB]
theorem comparison_isIso_of_isBilimit {S : Scheme.{u}}
    {X Y Y' : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack Y'] {f : X ⟶ Y} {g : Y' ⟶ Y}
    (c : PseudoPullbackCone f g) [AlgebraicStack c.pt] (hc : c.IsBilimit)
    (hf : IsIso (comparison f)) : IsIso (comparison c.snd) :=
  sorry

end AlgebraicGeometry.AlgebraicStack.Inertia
