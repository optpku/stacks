/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.Birational.GenericPointStalk
import StacksCheckRecall

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 29.50.6: for irreducible schemes `X` and `Y` locally of finite presentation over `S`,
`S`-birationality, isomorphic nonempty open subschemes over `S`, and compatible isomorphism of
their generic-point local rings over the stalk at their common image in `S` are equivalent. -/
@[stacks 0BAD] #check
  (AlgebraicGeometry.Scheme.birationalOver_tfae_of_locallyOfFinitePresentation :
    ∀ (S X Y : Scheme.{u}) [X.Over S] [Y.Over S]
      [IrreducibleSpace X] [IrreducibleSpace Y]
      [LocallyOfFinitePresentation (X ↘ S)] [LocallyOfFinitePresentation (Y ↘ S)],
      List.TFAE
        [ AlgebraicGeometry.Scheme.BirationalOver (X ↘ S) (Y ↘ S)
        , AlgebraicGeometry.HasIsomorphicNonemptyOpenSubschemesOver S X Y
        , AlgebraicGeometry.HasIsomorphicGenericPointsOver S X Y
        ])
