/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.EtaleComparison.Derived

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open AlgebraicGeometry.StandardTopology
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale
open RingedSite.Hom

noncomputable section

universe u

/- Lemma 59.101.2 (1): the canonical comparison from ordinary étale pullback to the derived
fppf direct image of ordinary fppf pullback is an isomorphism. -/
@[stacks 0DEX] #check
  (AlgebraicGeometry.Scheme.Etale.ModuleComparison.topologyComparison_isIso :
    ∀ (S : Scheme.{u}) (F : RingedSite.ModuleCat.{u} (Small.ringedSite S))
      [F.IsQuasicoherent],
      IsIso (AlgebraicGeometry.Scheme.Etale.ModuleComparison.topologyComparison S F))

/- Lemma 59.101.2 (2): the canonical comparison from the original small-étale module to the
derived fppf direct image of its ordinary fppf pullback is an isomorphism. -/
@[stacks 0DEX] #check
  (AlgebraicGeometry.Scheme.Etale.ModuleComparison.restrictionComparison_isIso :
    ∀ (S : Scheme.{u}) (F : RingedSite.ModuleCat.{u} (Small.ringedSite S))
      [F.IsQuasicoherent],
      IsIso (AlgebraicGeometry.Scheme.Etale.ModuleComparison.restrictionComparison S F))

end

end
