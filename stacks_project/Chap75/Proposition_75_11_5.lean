module

import StacksCheckRecall
public import stacks_project.Chap75.Proposition_75_11_5_Comparison

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

universe u

/- Proposition 75.11.5. Let `S` be a scheme. Let `X` be a quasi-compact algebraic space
over `S` with affine diagonal over `ℤ` (as in Properties of Spaces, Definition 66.3.1).
Then the functor 75.5.1.1,
`comparison X : DerivedCategory (QCoh X) ⥤ DerivedQCoh X`, is an equivalence with
quasi-inverse given by `RQ_X`, identified with
`inclusion X ⋙ QCoh.Derived.coherator X`. -/
@[stacks 08H1] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.comparison_isQuasiInverse_of_compact_affineDiagonal :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsQuasiCompact X] [IsAbsolutelyAffineDiagonal X],
      (DerivedQCoh.comparison X).IsQuasiInverse
        (DerivedQCoh.inclusion X ⋙ QCoh.Derived.coherator X))

/- The equivalence clause of Proposition 75.11.5. -/
#check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.comparisonIsEquivalenceOfCompactAffineDiagonal :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) [IsQuasiCompact X] [IsAbsolutelyAffineDiagonal X],
      (DerivedQCoh.comparison X).IsEquivalence)
