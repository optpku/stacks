module

public import Mathlib.Data.Finite.Defs
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Lemma_67_27_6_LocallyQuasiFinite
public import stacks_project.Chap68.«68_18_0_2_Fibre»

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Points

/-- Lemma 68.18.4: In the cartesian square of algebraic spaces over `S` with
legs `p : W ⟶ X`, `q : W ⟶ Z`, `f : X ⟶ Y`, and `g : Z ⟶ Y`, the pair-fibre
`fibre p q x z` is finite if `f` is of finite type and `f` is quasi-finite at
`x`, whenever `x` and `z` have the same image in `Points Y`. -/
@[stacks 0AC6]
theorem fibre_finite_of_finiteType_quasiFiniteAt
    {S : Scheme.{u}} {W X Y Z : AlgebraicSpace S}
    {p : W ⟶ X} {q : W ⟶ Z} {f : X ⟶ Y} {g : Z ⟶ Y}
    (h : IsPullback p q f g) [FiniteType f] (x : Points X) (z : Points Z)
    (hx : QuasiFiniteAt f x) (hy : map f x = map g z) :
    (fibre p q x z).Finite :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Points
