/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.ZariskiSite.ModuleEquivalence
import StacksCheckRecall

universe u

/- Remark 35.8.3: sheaves of modules on the small Zariski ringed site of a scheme agree with
sheaves of modules on its ringed space. -/
@[stacks 03FG] #check
  (AlgebraicGeometry.Scheme.smallZariskiModulePushforward_isEquivalence :
    (S : AlgebraicGeometry.Scheme.{u}) →
      (AlgebraicGeometry.Scheme.smallZariskiRingedSiteHom S).modulePushforward.{u}.IsEquivalence)
