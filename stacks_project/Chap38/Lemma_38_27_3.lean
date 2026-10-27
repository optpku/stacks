/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
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
fibres of dimension `d` and a finitely presented module `ℱ`, the canonical map from the
clopen-partition coproduct of generic-point rank functors through some bound `c` to the
flat-in-dimensions functor is an isomorphism, on all test schemes over `S`. -/
@[stacks 05UE] #check
  (AlgebraicGeometry.Scheme.Flattening.existsFlatInDimensionsIsoRankCoproduct f ℱ d :
    ∃ c : ℕ, IsIso (rankCoproductToFlatInDimensions f ℱ d c))

end AlgebraicGeometry.Scheme.Flattening
