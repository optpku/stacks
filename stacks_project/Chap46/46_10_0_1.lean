/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Restriction
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u

/- 46.10.0.1: the canonical restriction is a morphism of ringed sites from the
big `τ`-site of `S` to the small Zariski site of `S`. -/
@[stacks 070U] #check
  (AlgebraicGeometry.Scheme.SiteRestriction.bigToZariski :
    ∀ (τ : StandardTopology) (S : Scheme.{u}),
      RingedSite.Hom (StandardTopology.Big.ringedSite τ S)
        (Scheme.Zariski.Small.ringedSite S))
