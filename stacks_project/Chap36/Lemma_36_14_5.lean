/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.ApproximationByPerfectComplexes.OpenCover

@[expose] public section

open TopologicalSpace

universe u

/- Lemma 36.14.5: if a scheme `X` is covered by a quasi-compact open `U` and an affine
open `V`, with `U ⊓ V` quasi-compact, then approximation by perfect complexes on
`U.toScheme` implies approximation by perfect complexes on `X`. -/
@[stacks 08ER] #check
  (AlgebraicGeometry.Scheme.HasApproximationByPerfectComplexes.of_union :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} (U : X.Opens) (V : X.affineOpens),
      U ⊔ V = ⊤ → IsCompact (U : Set X) →
      IsCompact ((U ⊓ V : X.Opens) : Set X) →
      AlgebraicGeometry.Scheme.HasApproximationByPerfectComplexes U.toScheme →
      AlgebraicGeometry.Scheme.HasApproximationByPerfectComplexes X)
