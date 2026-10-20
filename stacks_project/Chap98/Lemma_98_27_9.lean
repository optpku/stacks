/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Contraction.Separation
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.SchemeRealization
open AlgebraicGeometry.AlgebraicSpace.ContractionSituation
open AlgebraicGeometry.Scheme.Over

universe u

/- Lemma 98.27.9: In Situation 98.27.1, if `X' ⟶ S` and `W ⟶ S` are
separated, the diagonal of the contraction functor is representable by closed
immersions. -/
@[stacks 0GHF] #check
  (AlgebraicGeometry.AlgebraicSpace.ContractionSituation.isClosedImmersion_diagonal :
    ∀ {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]
      (σ : ContractionSituation S)
      [Separated (toBase σ.X')] [FormalAlgebraicSpace.Separated (toBaseW σ)],
      ((MorphismProperty.over
          (@AlgebraicGeometry.IsClosedImmersion : MorphismProperty Scheme.{u})).inverseImage
        (locallyNoetherian S).ι).relative uliftYoneda.{u + 1} (Limits.diag σ.functor))
