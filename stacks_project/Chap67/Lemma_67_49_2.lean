/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap67.Lemma_67_49_1_FiniteComponents

/-!
# Locally Noetherian algebraic spaces have finite irreducible components on compact opens

A locally Noetherian algebraic space satisfies the equivalent conditions of
Lemma 67.49.1.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace HasFiniteIrreducibleComponentsOnCompactOpens

/-- Lemma 67.49.2: let `S` be a scheme. Let `X` be a locally Noetherian algebraic
space over `S`. Then `X` satisfies the equivalent conditions of Lemma 67.49.1,
recorded as `HasFiniteIrreducibleComponentsOnCompactOpens X`. -/
@[stacks 0GMB, instance]
instance instOfIsLocallyNoetherian {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsLocallyNoetherian X] : HasFiniteIrreducibleComponentsOnCompactOpens X :=
  sorry

end HasFiniteIrreducibleComponentsOnCompactOpens

end AlgebraicGeometry.AlgebraicSpace
