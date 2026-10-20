/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Perfect.Retracts
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.47.8

The retract and binary-biproduct APIs for perfect derived module sheaves are owned by
`RingedSite.Hom.ModuleDerived`; this file is only their tagged Chapter 21 source entry.
-/

/- Lemma 21.47.8 (08GA): if a binary biproduct of derived `𝒪_X`-modules is perfect, then both
summands are perfect. -/
@[stacks 08GA] #check @RingedSite.Hom.ModuleDerived.isPerfect_summands_of_biprod

#check @RingedSite.Hom.ModuleDerived.isPerfect_isStableUnderRetracts
#check @RingedSite.Hom.ModuleDerived.isPerfect_left_of_biprod
#check @RingedSite.Hom.ModuleDerived.isPerfect_right_of_biprod

end
