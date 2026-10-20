/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Localization.Adjunction
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.20.8

The exact localization adjunction on module sheaves descends through the canonical derived
localizations.
-/

/- Lemma 21.20.8 (08FJ): derived extension by zero is left adjoint to derived restriction. -/
@[stacks 08FJ]
#check @SheafOfModules.RingedSite.Localization.derivedAdjunction

#check @CategoryTheory.Adjunction.mapDerivedCategory
#check @SheafOfModules.RingedSite.Localization.lowerShriekDerived
#check @SheafOfModules.RingedSite.Localization.restrictionDerived
#check @SheafOfModules.RingedSite.Localization.lowerShriekDerived.isLeftAdjoint
#check @SheafOfModules.RingedSite.Localization.restrictionDerived.isRightAdjoint
