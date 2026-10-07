module

public import stacks_project.Chap67.Lemma_67_49_5_Normalization
public import stacks_project.Chap68.Definition_68_22_1_GenericPoints

/-!
# Absolute normalization of decent algebraic spaces

A decent algebraic space with finitely many irreducible components satisfies the
compact-opens hypothesis needed to form `X.normalization`, and that
normalization remains decent with finitely many irreducible components.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace HasFiniteIrreducibleComponentsOnCompactOpens

/-- A decent algebraic space with finitely many irreducible components has finitely
many irreducible components on compact opens, so `X.normalization` is defined. -/
instance of_isDecent {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsDecent X] [HasFiniteIrreducibleComponents X] :
    HasFiniteIrreducibleComponentsOnCompactOpens X :=
  sorry

end HasFiniteIrreducibleComponentsOnCompactOpens

/-- The absolute normalization of a decent algebraic space with finitely many
irreducible components is decent. -/
instance instIsDecent_normalization {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsDecent X] [HasFiniteIrreducibleComponents X] :
    IsDecent X.normalization :=
  sorry

/-- The absolute normalization of a decent algebraic space with finitely many
irreducible components has finitely many irreducible components. -/
instance instHasFiniteIrreducibleComponents_normalization {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsDecent X] [HasFiniteIrreducibleComponents X] :
    HasFiniteIrreducibleComponents X.normalization :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
