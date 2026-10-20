/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.ClosedPointFiber.Splitting
import StacksCheckRecall

/-!
# Theorem 15.128.5 (0GVC)

The source-faithful local free-summand theorem and its visible-fiber companion are owned by
`ReasLib.Algebra.Module.ClosedPointFiber.Splitting`.

@stack 0GVC
-/

@[expose] public section

@[stacks 0GVC "local free-summand hypothesis"]
#check @Module.ClosedFiber.HasLocalFreeSummandRankGT

@[stacks 0GVC "splitting a free rank-one summand"]
#check @Module.ClosedFiber.existsLinearEquivProdOfLocalFreeSummandRankGT

#check @Module.ClosedFiber.hasLocalFreeSummandRankGT_iff_finrank_visible
#check @Module.ClosedFiber.existsLinearEquivProdOfFinrankVisibleGTDimension
