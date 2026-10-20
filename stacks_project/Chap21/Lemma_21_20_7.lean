/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Derived.UnderlyingComparison
public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Derived.UnderlyingSectionsComparison
public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Derived.UnderlyingPushforwardComparison
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.20.7

The three comparisons are owned by the reusable `RingedSite.Hom.ModuleSections` API. This file
keeps the Stacks label and recalls each canonical morphism together with its natural isomorphism
and universal-property specification.
-/

/- Lemma 21.20.7 (0D6J): for a ringed site `X`, a derived module `K`, and an object `U : X`,
the canonical maps

* `RΓ(X, K) ⟶ RΓ(X, K_ab)`,
* `RΓ(U, K) ⟶ RΓ(U, K_ab)`, and
* `Rf_* K ⟶ Rf_*(K_ab)`

are isomorphisms in the corresponding derived categories.  The reusable formal owners are split
by mathematical role: global sections, objectwise sections, and direct image. -/

/- Lemma 21.20.7 (0D6J) (1): derived global sections after forgetting module scalars. -/
@[stacks 0D6J "(1)"]
#check @RingedSite.Hom.ModuleSections.globalComparison

#check @RingedSite.Hom.ModuleSections.globalIso
#check @RingedSite.Hom.ModuleSections.globalComparison_fac_app

/- Lemma 21.20.7 (0D6J) (2): derived sections over an object after forgetting module scalars. -/
@[stacks 0D6J "(2)"]
#check @RingedSite.Hom.ModuleSections.sectionsComparison

#check @RingedSite.Hom.ModuleSections.sectionsIso
#check @RingedSite.Hom.ModuleSections.sectionsComparison_fac_app

/- Lemma 21.20.7 (0D6J) (3): derived direct image after forgetting module scalars. -/
@[stacks 0D6J "(3)"]
#check @RingedSite.Hom.ModuleSections.pushforwardComparison

#check @RingedSite.Hom.ModuleSections.pushforwardIso
#check @RingedSite.Hom.ModuleSections.pushforwardComparison_fac_app
