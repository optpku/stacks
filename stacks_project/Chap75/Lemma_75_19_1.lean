module

public import stacks_project.Chap75.Lemma_75_19_1_Instances
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/- Lemma 75.19.1: for a quasi-compact and quasi-separated algebraic space `X` over a
scheme `S`, the inclusion `D_QCoh(𝒪_X) ⟶ D(𝒪_X)` has a right adjoint. -/
@[stacks 0CR4] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.inclusionIsLeftAdjoint :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
      [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X],
      (inclusion X).IsLeftAdjoint)

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
