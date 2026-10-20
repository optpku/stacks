/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.Smooth
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 29.36.5

The reusable pointwise smooth/étale API is maintained in
`ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.Smooth`.
-/

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 29.36.5: pointwise étaleness is smoothness plus unramifiedness. -/
@[stacks 02GK] #check
  (AlgebraicGeometry.Scheme.Hom.etaleAt_iff_smoothAt_and_unramifiedAt :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) (x : X),
      f.EtaleAt x ↔ f.SmoothAt x ∧ f.UnramifiedAt x)
