/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Finiteness

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 31.2.5: let `X` be a locally Noetherian scheme and let `ℱ` be a coherent
`𝒪_X`-module. Then `Ass(ℱ) ∩ U` is finite for every quasi-compact open `U ⊆ X`. -/
@[stacks 05AF] #check
  (AlgebraicGeometry.Scheme.Modules.associatedPoints_inter_quasiCompactOpen_finite :
    ∀ {X : Scheme.{u}} [IsLocallyNoetherian X] (ℱ : X.Modules) [ℱ.IsCoherent]
      (U : X.Opens), IsCompact (U : Set X) →
        (Scheme.Modules.associatedPoints ℱ ∩ (U : Set X)).Finite)
