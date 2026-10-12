/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact
public import stacks_project.Chap67.Definition_67_20_2_Affine
public import stacks_project.Chap75.Definition_75_9_1_Square
public import stacks_project.Chap75.Definition_75_14_2_Approximation

/-!
# Approximation along an elementary distinguished square

If `(U ⊂ X, f : V ⟶ X)` is an elementary distinguished square of algebraic
spaces with `U` quasi-compact, `V` affine, and `U ×_X V` quasi-compact, then
approximation by perfect complexes on `U` implies the same on `X`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.HasApproximationByPerfectComplexes

/-- Lemma 75.14.6: let `S` be a scheme and let `(U ⊂ X, f : V ⟶ X)` be an
elementary distinguished square of algebraic spaces over `S`. Assume `U` is
quasi-compact, `V` is affine, and `U ×_X V` is quasi-compact. If approximation
by perfect complexes holds on `U`, then approximation by perfect complexes
holds on `X`. The source morphism `j : V → X` is this étale map `f`, and
`U ×_X V` is `pullback j f`. -/
@[stacks 08HN]
theorem of_isElementaryDistinguishedSquare
    {S : Scheme.{u}} {U V X : AlgebraicSpace S} (j : U ⟶ X) (f : V ⟶ X)
    [IsElementaryDistinguishedSquare j f] [IsQuasiCompact U] [IsAffine V]
    [IsQuasiCompact (pullback j f)] (hU : HasApproximationByPerfectComplexes U) :
    HasApproximationByPerfectComplexes X :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.HasApproximationByPerfectComplexes
