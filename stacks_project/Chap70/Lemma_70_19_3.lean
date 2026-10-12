/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap70.Lemma_70_19_3_BaseChange
public import stacks_project.Chap70.Lemma_70_19_3_FinitePresentationIsoOverOpen
public import stacks_project.Chap70.Lemma_70_19_3_Henselization

/-!
# Equivalence of modifications after base change to the henselization

For a decent algebraic space, finite-presentation morphisms that are
isomorphisms away from a closed point with quasi-compact complement are
equivalent, after base change, to the corresponding morphisms over the
punctured henselization.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 70.19.3: let `S` be a scheme and `X` a decent algebraic space over `S`.
Let `x ∈ |X|` be a closed point such that `U = X \ {x} ⟶ X` is quasi-compact.
With `V = Spec(𝒪_{X,x}^h) \ {𝔪_x^h}`, the base-change functor
`puncturedHenselizationBaseChange X hx` from finite-presentation morphisms
`Y ⟶ X` that are isomorphisms over `U` to finite-presentation morphisms
`Y ⟶ Spec(𝒪_{X,x}^h)` that are isomorphisms over `V` is an equivalence of
categories. -/
@[stacks 0BH0, instance]
instance puncturedHenselizationBaseChange_isEquivalence {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsDecent X] {x : Points X}
    (hx : x ∈ closedPoints (Points X))
    [QuasiCompact (closedPointComplementι X hx)] :
    (puncturedHenselizationBaseChange X hx).IsEquivalence :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
