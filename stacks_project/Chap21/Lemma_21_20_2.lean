/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Localization.Cohomology
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.20.2

The localization `X/U` has terminal object `Over.mk (𝟙 U)`, and cohomology over `U` is
identified with cohomology there.  The reusable statement is owned by ReasLib.
-/

/- Lemma 21.20.2 (0D6F): cohomology over `U` is cohomology on the localization `X/U`. -/
@[stacks 0D6F]
#check @RingedSite.Hom.ModuleDerived.Localization.cohomologyOverObject_isomorphic_localization

#check @RingedSite.Hom.ModuleDerived.Localization.localizedCohomologyOverObject
#check @RingedSite.Hom.ModuleDerived.cohomologyOverObject
#check @RingedSite.Hom.localizedRestrictionDerived
#check @RingedSite.Hom.ModuleDerived.underlyingPresheafDerived

