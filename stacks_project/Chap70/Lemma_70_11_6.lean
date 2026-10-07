module

public import stacks_project.Chap70.Lemma_70_11_6_Factorization
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace
open scoped AlgebraicGeometry

universe u

/- Lemma 70.11.6: a locally of finite type morphism `f : X ⟶ Y` of algebraic
spaces over a scheme `S`, with `X` and `Y` quasi-compact and quasi-separated,
factors as a closed immersion `X ⟶ X'` over `Y` followed by a morphism
`X' ⟶ Y` of finite presentation. -/
@[stacks 0872] #check
  (AlgebraicGeometry.AlgebraicSpace.exists_closedImmersion_factorization_of_locallyOfFiniteType :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [AlgebraicSpace.LocallyOfFiniteType f]
      [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
      [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y],
      (MorphismProperty.comp
        (@AlgebraicSpace.IsClosedImmersion S : MorphismProperty (AlgebraicSpace S))
        (@AlgebraicSpace.FinitePresentation S : MorphismProperty (AlgebraicSpace S))) f)
