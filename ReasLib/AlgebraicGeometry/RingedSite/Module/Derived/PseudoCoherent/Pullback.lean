/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.PseudoCoherent
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Pullback of pseudo-coherent derived module sheaves

Pseudo-coherence is preserved by the total derived inverse-image functor.  The public statement
depends only on the canonical derived-pullback gate and the pseudo-coherence predicates; local
cover and localization data belong to the proof of this theorem rather than its interface.
-/

open CategoryTheory ComplexShape
open RingedSite.Hom (ModuleDerived ModuleQis modulePullbackDerived modulePullbackToDerived)

noncomputable section

universe uX vX uY vY w

set_option checkBinderAnnotations false

namespace RingedSite.Hom.ModuleDerived.IsMPseudoCoherent

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
variable [UnivLE.{max uX vX, w}] [UnivLE.{max uY vY, w}]
variable [∀ U : X,
  HasWeakSheafify (X.localization U).siteTopology AddCommGrpCat.{w}]
variable [∀ U : X,
  (X.localization U).siteTopology.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ U : Y,
  HasWeakSheafify (Y.localization U).siteTopology AddCommGrpCat.{w}]
variable [∀ U : Y,
  (Y.localization U).siteTopology.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Lemma 21.45.3: derived pullback preserves `m`-pseudo-coherence. -/
@[stacks 08H4]
theorem pullback (f : RingedSite.Hom X Y)
    [(f.modulePushforward.{w}).IsRightAdjoint]
    [Functor.HasLeftDerivedFunctor
      (modulePullbackToDerived.{w} f) (ModuleQis.{w} Y)]
    {E : ModuleDerived.{w} Y} {m : ℤ} (hE : E.IsMPseudoCoherent m) :
    ((modulePullbackDerived.{w} f).obj E).IsMPseudoCoherent m := sorry

end RingedSite.Hom.ModuleDerived.IsMPseudoCoherent
