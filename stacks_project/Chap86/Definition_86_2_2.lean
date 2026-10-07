module

public import stacks_project.Chap86.Definition_86_2_2_DualizingComplex
import StacksCheckRecall

universe u

/- Definition 86.2.2: let `S` be a scheme. Let `X` be a locally Noetherian algebraic space
over `S`. An object `K` of `D_QCoh(𝒪_X)` is called a dualizing complex if `K` satisfies
the equivalent conditions of Lemma 86.2.1. -/
@[stacks 0E4Z] #check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.IsDualizingComplex :
  {S : AlgebraicGeometry.Scheme.{u}} →
    {X : AlgebraicGeometry.AlgebraicSpace S} →
      [AlgebraicGeometry.AlgebraicSpace.IsLocallyNoetherian X] →
        AlgebraicGeometry.AlgebraicSpace.DerivedQCoh X → Prop)
