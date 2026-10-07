module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap67.Definition_67_20_2_Affine
public import stacks_project.Chap76.Lemma_76_9_2_Thickening
public import stacks_project.Chap81.«81_6_5_1_Cube»

/-!
# Equation 81.6.5.1

A pushout of algebraic spaces along a thickening and an affine morphism admits a commutative
cube against a chosen scheme atlas, with pushout front and back faces, cartesian remaining
faces, and surjective étale northeast arrows.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.PushoutAlongThickening

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.PushoutAlongThickening

/-- 81.6.5.1: Let `S` be a scheme, let `i : X ⟶ X'` be a thickening of algebraic spaces over
`S`, and let `f : X ⟶ Y` be an affine morphism of algebraic spaces over `S`. If
`i' : X' ⟶ Y'` and `g : Y ⟶ Y'` exhibit `Y'` as the pushout of `i` and `f`, then for any
scheme `Y1` over `S` and surjective étale morphism `πY : ofOver Y1 ⟶ Y` there is a
commutative cube with scheme vertices `X1`, `X1'`, `Y1`, `Y1'` over `S`, algebraic space
vertices `X`, `X'`, `Y`, `Y'`, front and back faces pushouts, the other four faces
cartesian, and northeast arrows surjective étale. -/
@[stacks 07W1]
theorem exists_cube {S : Scheme.{u}} {X X' Y Y' : AlgebraicSpace S}
    (i : X ⟶ X') (f : X ⟶ Y) (i' : X' ⟶ Y') (g : Y ⟶ Y')
    [IsThickening i] [Affine f] (h : IsPushout i f i' g)
    {Y1 : Over S} (πY : ofOver Y1 ⟶ Y) [Etale πY] [Surjective πY] :
    Nonempty (Cube i f i' g πY) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.PushoutAlongThickening
