/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Zariski.Flat

@[expose] public section

universe u

/- Lemma 35.10.1: for every scheme `S`, the canonical morphism from its small étale
ringed site to its small Zariski ringed site is flat. -/
@[stacks 0GNA] #check
  (AlgebraicGeometry.Scheme.SiteRestriction.smallEtaleToZariski_isFlat :
    ∀ (S : AlgebraicGeometry.Scheme.{u}),
      RingedSite.Hom.IsFlat.{u}
        (AlgebraicGeometry.Scheme.SiteRestriction.smallEtaleToZariski S))
