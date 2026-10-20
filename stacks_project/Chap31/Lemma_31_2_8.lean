/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Sections

universe u

/- Lemma 31.2.8: let `X` be a locally Noetherian scheme, let `ℱ` be a quasicoherent
`𝒪_X`-module, and let `U ⊆ X` be open. If every associated point of `ℱ` belongs to `U`, then
restriction from `Γ(X, ℱ)` to `Γ(U, ℱ)` is injective. -/
@[stacks 0B3L] #check
  (AlgebraicGeometry.Scheme.Modules.injective_restrictionToOpen_of_associatedPoints_subset :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} (ℱ : X.Modules) [ℱ.IsQuasicoherent]
      [AlgebraicGeometry.IsLocallyNoetherian X] (U : X.Opens),
      AlgebraicGeometry.Scheme.Modules.associatedPoints ℱ ⊆ (U : Set X) →
        Function.Injective (ℱ.val.map (TopologicalSpace.Opens.leTop U).op))
