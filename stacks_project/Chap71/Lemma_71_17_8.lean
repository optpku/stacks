/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Lemma_67_49_1_FiniteComponents
public import stacks_project.Chap71.Definition_71_17_1_Blowup

/-!
# Finite irreducible components on compact opens after blowup
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Blowup

/-- Lemma 71.17.8: let `S` be a scheme. Let `X` be an algebraic space over `S`.
Let `π : along Z` be a chosen blowup of `X` in a closed subspace `Z`, with
blowup morphism `b = π.hom` and blowup space `X' = π.space`. If `X` satisfies
the equivalent conditions of Morphisms of Spaces Lemma 67.49.1, packaged as
`HasFiniteIrreducibleComponentsOnCompactOpens X`, then so does `π.space`. -/
@[stacks 0BH1]
instance instHasFiniteIrreducibleComponentsOnCompactOpens
    {S : Scheme.{u}} {X : AlgebraicSpace S} (Z : ClosedSubspace X)
    (π : along Z) [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    HasFiniteIrreducibleComponentsOnCompactOpens π.space := sorry

end AlgebraicGeometry.AlgebraicSpace.Blowup
