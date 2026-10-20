module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.ArtinCriterion
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Groupoids
open AlgebraicGeometry.GroupoidsOver
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 98.17.1: let `S` be a locally Noetherian scheme and let `X` be a
category fibred in groupoids over `(Sch/S)_fppf`. Assume (1) the diagonal
`Δ : X ⟶ X × X` is representable by algebraic spaces, (2) `X` satisfies axioms
[-1], [0], [1], [2], [3], (3) every formal object of `X` is effective, (4) `X`
satisfies openness of versality, and (5) `𝒪_{S,s}` is a G-ring for every finite
type point `s` of `S`. Then `X` is an algebraic stack. -/
@[stacks 07Y4] #check (AlgebraicGeometry.AlgebraicStack.of_representableDiagonal :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X : GroupoidsOver S}
    [IsStack.InGroupoids (Scheme.etaleTopology.over S) X.p]
    [LimitPreserving X] [HasRimSchlessinger X]
    [HasFiniteDimensionalPredeformations X] [OpennessOfVersality X]
    [HasBoundedFiniteTypeFibers X]
    (h_diag :
      relativelyRepresentableByAlgebraicSpaces
        (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X))
    (h_eff : ∀ ξ : FormalObject X, FormalObject.IsEffective ξ)
    (hG : ∀ s : S, IsFiniteTypePoint s → IsGRing (S.presheaf.stalk s)),
    AlgebraicStack X)

end AlgebraicGeometry.AlgebraicStack
