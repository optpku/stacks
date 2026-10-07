module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Normalization.Nagata.EmptyFiber

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 29.53.16: let `f : Y ⟶ X` be a finite-type morphism of schemes with `Y` reduced and
`X` Nagata. If `x'` is a one-dimensional point of the normalization of `X` in `Y` and the fiber
of `Y ⟶ f.normalization` over `x'` is empty, then the stalk at `x'` is a discrete valuation
ring. -/
@[stacks 0BXB] #check
  (AlgebraicGeometry.Scheme.Hom.isDiscreteValuationRing_stalk_normalization_of_empty_fiber :
    ∀ {Y X : Scheme.{u}} (f : Y ⟶ X) [Scheme.Hom.FiniteType f] [IsReduced Y]
      [Scheme.Nagata X] (x' : f.normalization),
      ringKrullDim (f.normalization.presheaf.stalk x') = 1 →
        IsEmpty (f.toNormalization.fiber x') →
          ∃ (_ : IsDomain (f.normalization.presheaf.stalk x')),
            IsDiscreteValuationRing (f.normalization.presheaf.stalk x'))
