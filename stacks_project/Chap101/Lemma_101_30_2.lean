module

public import stacks_project.Chap101.Lemma_101_30_1

/-!
# Spectral spaces of quasi-compact quasi-separated algebraic stacks

A quasi-compact quasi-separated algebraic stack has spectral space of points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 101.30.2: Let `X` be a quasi-compact and quasi-separated algebraic stack.
Then `|X|` is a spectral topological space. -/
@[stacks 0DQP]
instance instSpectralSpacePoints {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] [IsQuasiCompact X] [IsQuasiSeparated X] :
    SpectralSpace (Points X) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
