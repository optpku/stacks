module

import StacksCheckRecall
public import stacks_project.Chap75.Proposition_75_12_6_Comparison

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

universe u

/- Proposition 75.12.6. Let `S` be a scheme. Let `X` be a Noetherian algebraic space
over `S`. Then the functor 75.5.1.1,
`comparison X : DerivedCategory (QCoh X) ⥤ DerivedQCoh X`, is an equivalence with
quasi-inverse given by `RQ_X`, identified with
`inclusion X ⋙ QCoh.Derived.coherator X`. -/
@[stacks 09TN] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.comparison_isQuasiInverse_of_isNoetherian :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsNoetherian X],
      (DerivedQCoh.comparison X).IsQuasiInverse
        (DerivedQCoh.inclusion X ⋙ QCoh.Derived.coherator X))

/- The equivalence clause of Proposition 75.12.6. -/
#check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.comparisonIsEquivalence :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) [IsNoetherian X],
      (DerivedQCoh.comparison X).IsEquivalence)
