/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DeRham.DifferentialOperator
import StacksCheckRecall

@[expose] public section

/- Lemma 17.30.3 (0G3Y): each differential in the relative de Rham
complex of a morphism of commutative ring sheaves is a differential operator
of order at most one. -/
@[stacks 0G3Y]
#check @SheafOfModules.RingedSite.DeRham.d_isOrderOne
