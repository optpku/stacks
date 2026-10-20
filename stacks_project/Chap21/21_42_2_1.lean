/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Flat.Generators
import StacksCheckRecall

@[expose] public section

/- 21.42.2.1 (08S1): every module sheaf admits a short exact kernel sequence whose middle
term is a coproduct of localized structure modules `j![𝒪, U]`. -/
@[stacks 08S1]
#check @SheafOfModules.RingedSite.exists_shortExact_coproduct_structureModule
