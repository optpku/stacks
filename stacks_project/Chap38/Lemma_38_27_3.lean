/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Flattening.RankDecomposition
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Flattening

variable {X S : Scheme.{u}} (f : X ⟶ S) (ℱ : X.Modules) (d : ℕ)
variable [IsAffine X] [IsAffine S] [Smooth f] [GeometricallyIrreducible f]
  [Scheme.Hom.RelativeDimension f d] [ℱ.IsFinitePresentation]

/- Lemma 38.27.3: for a smooth morphism of affine schemes with geometrically irreducible
fibres of dimension `d` and a finitely presented module `ℱ`, the flat-in-dimensions functor is
the finite coproduct of the generic-point rank functors through some bound `c`. -/
@[stacks 05UE] #check
  (AlgebraicGeometry.Scheme.Flattening.existsFlatInDimensionsIsoRankCoproduct f ℱ d :
    ∃ c : ℕ,
      Nonempty
        (flatInDimensionsFunctor f ℱ d ≅
          ∐ fun p : Fin (c + 1) ↦ freeAtGenericPointsFunctor f ℱ p))

end AlgebraicGeometry.Scheme.Flattening
