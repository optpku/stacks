/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Family.Regular

open AlgebraicGeometry CategoryTheory Limits
open scoped AlgebraicGeometry

universe u

/- Lemma 31.16.8: a quasi-compact regular scheme with affine diagonal has an ample family of
invertible modules. -/
@[stacks 0GML] #check
  (AlgebraicGeometry.Scheme.exists_ampleFamily_of_compact_regular_affineDiagonal :
    ∀ (X : Scheme.{u}) [CompactSpace X] [Scheme.Regular X]
      [IsAffineHom (prod.lift (𝟙 X) (𝟙 X))],
      ∃ (ι : Type u) (L : ι → X.Modules)
        (hL : ∀ i : ι, Scheme.Modules.Invertible (L i)),
          Scheme.Modules.AmpleFamily L)
