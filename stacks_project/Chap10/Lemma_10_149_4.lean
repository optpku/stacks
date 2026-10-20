/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Extension.Cotangent.BaseChange
public import ReasLib.RingTheory.Extension.FirstOrder.BaseChange
public import ReasLib.RingTheory.Extension.FirstOrder.Localization
public import ReasLib.RingTheory.Extension.Localization
import StacksCheckRecall

/-!
# Localization of Universal First-Order Thickenings

Base-ring localization is exposed through the stronger owner-level base-change
theorem.  Target localization has its own theorem and canonical cotangent map.

@stack 04EE
-/

@[expose] public section

/- Lemma 10.149.4 (1): universal first-order thickenings are preserved by
base change, hence in particular by localization of the base ring. -/
@[stacks 04EE "(1), base-ring localization"]
#check @Algebra.Extension.FirstOrder.IsUniversal.baseChange

/- The canonical cotangent comparison for a flat base change supplies the
conormal-module clause of (1). -/
@[stacks 04EE "(1), flat cotangent base change"]
#check @Algebra.Extension.tensorCotangentOfFlat

/- Lemma 10.149.4 (2): localizing the target preserves the universal
first-order thickening. -/
@[stacks 04EE "(2), target localization"]
#check @Algebra.Extension.FirstOrder.IsUniversal.localization

/- The canonical map realizes the localized conormal module without choosing
a parallel conormal carrier. -/
@[stacks 04EE "(2), extension morphism to target localization"]
#check @Algebra.Extension.TargetLocalization.hom

@[stacks 04EE "(2), localized extension kernel"]
#check @Algebra.Extension.TargetLocalization.ker_eq_map

@[stacks 04EE "(2), target-localization cotangent map"]
#check @Algebra.Extension.TargetLocalization.cotangentMap

@[stacks 04EE "(2), localized conormal module"]
#check @Algebra.Extension.TargetLocalization.cotangentMap_isLocalizedModule
