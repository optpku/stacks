/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Pushforward.Cohomology
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.20.6

Derived direct image identifies the restricted source cohomology presheaf with the target
cohomology presheaf; after sheafification this recovers the target cohomology sheaf.
-/

/- Lemma 21.20.6 (0D6I): the sheaf associated to `V ↦ H^q(f(V), K)` is the underlying
additive sheaf of `𝓗^q(Rf_*K)`. -/
@[stacks 0D6I]
#check @RingedSite.Hom.modulePushforwardDerived.cohomologySheafification_isomorphic

#check @RingedSite.Hom.modulePushforwardDerived.cohomologyPresheaf_isomorphic
#check @RingedSite.Hom.ModuleDerived.cohomologyPresheaf
#check @RingedSite.Hom.ModuleDerived.underlyingCohomologySheaf
#check @RingedSite.Hom.modulePushforwardDerived
