module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlongSubspace
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Definition 87.38.1: Let `S` be a scheme. Let `X` be an algebraic space over `S`.
Let `Z ⊂ X` be a closed subspace and denote `Z_n ⊂ X` the `n`th order infinitesimal
neighbourhood `Hom.InfinitesimalNeighbourhood.space i n`. The formal algebraic space
`completionAlongSubspace i`, the colimit of the spaces `Z_n` (see Lemma 87.36.2),
is called the completion of `X` along `Z`. -/
@[stacks 0GXU] #check (AlgebraicGeometry.AlgebraicSpace.completionAlongSubspace :
  ∀ {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X)
    [AlgebraicSpace.IsClosedImmersion i], (Over S)ᵒᵖ ⥤ Type u)
