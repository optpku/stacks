module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicStack.ResidualGerbe
public import stacks_project.Chap100.Lemma_100_9_10_Substack

/-!
# Existence and uniqueness of residual gerbes over a point

The three existence conditions are equivalent and imply uniqueness of the
reduced locally Noetherian strictly full singleton subcategory over the point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 100.11.7 (1): The three pointwise existence conditions are equivalent. -/
@[stacks 06MT] #check (AlgebraicGeometry.AlgebraicStack.existsMonoSingletonAt_tfae :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] (x : Points X),
    List.TFAE
      [ existsMonoSingletonAt X x
      , existsReducedMonoSingletonAt X x
      , existsMonoSurjectiveFlatSpecFieldAt X x ])

/- Lemma 100.11.7 (2): Under these conditions, the reduced locally Noetherian
strictly full singleton subcategory over the point exists and is unique. -/
@[stacks 06MT] #check (AlgebraicGeometry.AlgebraicStack.existsUnique_locallyNoetherian_strictlyFull_at :
    ∀ {S : Scheme.{u}}
    (X : GroupoidsOver S) [AlgebraicStack X] (x : Points X)
    (h : existsMonoSingletonAt X x),
    ∃ (P : ObjectProperty X.total)
      (h_fibered : Functor.IsFibered.InGroupoids (P.ι ⋙ X.p))
      (h_algebraicStack : AlgebraicStack (Substack.category X P h_fibered))
      (h_reduced : IsReduced (Substack.category X P h_fibered))
      (h_locallyNoetherian : IsLocallyNoetherian (Substack.category X P h_fibered))
      (h_nonempty : Nonempty (Points (Substack.category X P h_fibered)))
      (h_subsingleton : Subsingleton (Points (Substack.category X P h_fibered)))
      (h_strictlyFull : P.IsClosedUnderIsomorphisms)
      (h_image : Set.range (Points.map (Substack.inclusion X P h_fibered)) = {x}),
      ∀ (Q : ObjectProperty X.total)
        (hQ_fibered : Functor.IsFibered.InGroupoids (Q.ι ⋙ X.p))
        (hQ_algebraicStack : AlgebraicStack (Substack.category X Q hQ_fibered))
        (hQ_reduced : IsReduced (Substack.category X Q hQ_fibered))
        (hQ_locallyNoetherian : IsLocallyNoetherian (Substack.category X Q hQ_fibered))
        (hQ_nonempty : Nonempty (Points (Substack.category X Q hQ_fibered)))
        (hQ_subsingleton : Subsingleton (Points (Substack.category X Q hQ_fibered)))
        (hQ_strictlyFull : Q.IsClosedUnderIsomorphisms)
        (hQ_image : Set.range (Points.map (Substack.inclusion X Q hQ_fibered)) = {x}),
        Q = P)

end AlgebraicGeometry.AlgebraicStack
