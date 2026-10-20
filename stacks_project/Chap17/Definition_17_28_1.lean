/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Derivation
import StacksCheckRecall

@[expose] public section

/- Definition 17.28.1 (01UN): relative derivations of sheaves of commutative rings are the
site-generic relative derivations into a module sheaf. -/
@[stacks 01UN]
#check @SheafOfModules.RelativeDerivation
