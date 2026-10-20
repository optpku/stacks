/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.FiniteProjective
import StacksCheckRecall

@[expose] public section

/- Lemma 21.49.1 (0FPX): global sections identify finite-free-retract module sheaves with
finite-projective modules over the global-sections ring. -/
@[stacks 0FPX]
#check @RingedSite.Hom.finiteFreeRetractGlobalSections_isEquivalence

#check @RingedSite.Hom.finiteFreeRetractGlobalSections
#check @RingedSite.Hom.moduleGlobalSections_mem_finiteProjective
