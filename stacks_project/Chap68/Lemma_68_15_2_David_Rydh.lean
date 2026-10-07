module

public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap68.Lemma_68_12_8_Decent

/-!
# Locally separated algebraic spaces are decent

A locally separated algebraic space, in the absolute sense of
Definition 66.3.1, is decent.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 68.15.2 (David Rydh): A locally separated algebraic space, in the
absolute sense of Definition 66.3.1, is decent. -/
@[stacks 088J]
instance instIsDecent_of_isAbsolutelyLocallySeparated {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsAbsolutelyLocallySeparated X] : IsDecent X :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
