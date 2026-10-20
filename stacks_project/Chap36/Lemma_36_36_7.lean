/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Family.ResolutionProperty
import StacksCheckRecall

universe u v

/- Lemma 36.36.7: a scheme with an ample family of invertible modules has the resolution
property. -/
@[stacks 0GMM] #check
  (AlgebraicGeometry.Scheme.hasResolutionProperty_of_ampleFamily :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} {ι : Type v} (L : ι → X.Modules),
      AlgebraicGeometry.Scheme.Modules.AmpleFamily L →
        AlgebraicGeometry.Scheme.HasResolutionProperty X)
