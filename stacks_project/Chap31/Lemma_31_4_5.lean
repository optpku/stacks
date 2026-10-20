/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Closure.AssociatedPoints

open AlgebraicGeometry

universe u

/- Lemma 31.4.5: for an open subscheme `U` of a locally Noetherian scheme `X`, the following
are equivalent: `U` is scheme-theoretically dense; `U` is topologically dense and contains all
embedded points; and `U` contains all associated points. -/
@[stacks 083P] #check
  (AlgebraicGeometry.Scheme.schemeTheoreticallyDense_open_tfae_dense_embeddedPoints_associatedPoints :
    ∀ (X : Scheme.{u}) [IsLocallyNoetherian X] (U : X.Opens),
      List.TFAE [
        schemeTheoreticallyDense U,
        Dense (U : Set X) ∧ X.embeddedPoints ⊆ (U : Set X),
        X.associatedPoints ⊆ (U : Set X)
      ])
