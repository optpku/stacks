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

/- 75.4.0.1: the displayed morphism of ringed sites
ε : (X_étale, 𝒪_étale) ⟶ (X_Zar, 𝒪_X), identified with Descent's
id_small,étale,Zar. -/
@[stacks 08H7] #check
  (AlgebraicGeometry.Scheme.SiteRestriction.smallEtaleToZariski :
    ∀ (S : Scheme.{u}),
      RingedSite.Hom (Scheme.Etale.Small.ringedSite S)
        (Scheme.Zariski.Small.ringedSite S))
