module

public import stacks_project.Chap75.Lemma_75_13_1_FiniteType
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
