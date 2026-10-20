/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Zariski.FiniteType
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.Scheme.SiteRestriction

universe u

/- Lemma 75.13.1: for a scheme `X` and an `𝒪_X`-module `F`, `F` is of finite type on the
small Zariski ringed site if and only if `ε* F` is of finite type on the small étale
ringed site, where `ε` is `smallEtaleToZariski` as in 75.4.0.1. -/
@[stacks 08HD] #check
  (AlgebraicGeometry.Scheme.SiteRestriction.smallEtaleToZariski_isFiniteType_iff :
    ∀ {X : Scheme.{u}}
      (F : RingedSite.ModuleCat.{u} (Scheme.Zariski.Small.ringedSite X)),
      F.IsFiniteType ↔
        ((smallEtaleToZariski X).modulePullback.obj F).IsFiniteType)
