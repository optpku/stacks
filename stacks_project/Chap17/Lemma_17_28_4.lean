/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Differentials
import StacksCheckRecall

@[expose] public section

/- Lemma 17.28.4 (08TD): relative differentials are obtained by sheafifying the objectwise
presheaf of Kähler differentials. -/
@[stacks 08TD]
#check @SheafOfModules.RingedSite.relativeDifferentials_def

#check @TopCat.Sheaf.relativeDifferentials_def
