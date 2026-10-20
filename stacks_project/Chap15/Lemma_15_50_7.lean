/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.FormalFiber.GRing.Maximal
import StacksCheckRecall

/-!
# Lemma 15.50.7

@stack 07PT
-/

@[expose] public section

/- Lemma 15.50.7, tag `07PT`: a Noetherian ring is a G-ring exactly when each localization at a
maximal ideal has geometrically regular formal fibers. -/
@[stacks 07PT "maximal-local criterion for G-rings"]
#check @IsGRing.iff_forall_maximal_holdsOnFormalFibers

/- At a fixed maximal ideal, being a G-ring is equivalent to having geometrically regular formal
fibers. -/
#check @IsGRing.localizationAtMaximal_iff_holdsOnFormalFibers

/- The same criterion can be stated entirely in terms of G-rings at maximal localizations. -/
#check @IsGRing.iff_forall_localizationAtMaximal

/- The two directions are exposed separately for downstream construction and elimination. -/
#check @IsGRing.localizationAtMaximal
#check @IsGRing.of_localizationsAtMaximal
