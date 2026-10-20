/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.StrictlyPerfect.Pullback
import StacksCheckRecall

@[expose] public section

/- Lemma 20.46.4 (09U6): pullback along a morphism of ringed spaces preserves strictly perfect
complexes of modules. The mathematical owner lives in ReasLib; this file is the source index. -/
@[stacks 09U6] #check @AlgebraicGeometry.RingedSpace.CochainComplex.isStrictlyPerfect_pullback

#check @SheafOfModules.CochainComplex.IsStrictlyPerfect.pullback
#check @CochainComplex.boundedTermsIn_map
#check @SheafOfModules.finiteFreeRetractModuleProperty_pullback

end
