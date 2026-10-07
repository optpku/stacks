module

public import stacks_project.Chap75.Lemma_75_28_4_FiniteLocallyFree
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 75.28.4: a surjective finite locally free morphism of algebraic spaces
over a scheme transfers the resolution property from its source to its target. -/
@[stacks 0GUV] #check
  (AlgebraicGeometry.AlgebraicSpace.hasResolutionProperty_of_surjective_finiteLocallyFree :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S}
      (f : X ⟶ Y) [AlgebraicGeometry.AlgebraicSpace.Surjective f]
      [AlgebraicGeometry.AlgebraicSpace.FiniteLocallyFree f],
      AlgebraicGeometry.AlgebraicSpace.HasResolutionProperty X →
        AlgebraicGeometry.AlgebraicSpace.HasResolutionProperty Y)
