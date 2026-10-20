/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.CohenMacaulay.EmbeddedPoints

open AlgebraicGeometry

universe u

/- Lemma 31.4.4: a locally Noetherian scheme of topological Krull dimension at most one is
Cohen-Macaulay if and only if it has no embedded points. -/
@[stacks 0BXG] #check
  (AlgebraicGeometry.Scheme.cohenMacaulay_iff_embeddedPoints_eq_empty_of_topologicalKrullDim_le_one :
    ∀ (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsLocallyNoetherian X],
      topologicalKrullDim X ≤ 1 →
        (AlgebraicGeometry.Scheme.CohenMacaulay X ↔ X.embeddedPoints = (∅ : Set X)))
