/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.ClosedPointFiber.Splitting
import StacksCheckRecall

/-!
# Lemma 15.128.3 (0GVA)

Interpolation of visible classes at finitely many pairwise distinct closed points is owned by
`ReasLib.Algebra.Module.ClosedPointFiber.Splitting`.

@stack 0GVA
-/

@[expose] public section

@[stacks 0GVA "interpolation of visible fiber classes"]
#check @Module.ClosedFiber.existsSectionWithPrescribedVisibleClasses
