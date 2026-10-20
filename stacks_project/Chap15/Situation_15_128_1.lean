/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.ClosedPointFiber
import StacksCheckRecall

/-!
# Situation 15.128.1 (0GV8)

The quotient fiber, its residue-field structure, the tensor comparison, and the image of a section
are owned by `ReasLib.Algebra.Module.ClosedPointFiber`.

@stack 0GV8
-/

@[expose] public section

open scoped ClosedPointFiber

@[stacks 0GV8 "closed-point module fiber"]
#check @Module.ClosedPointFiber

@[stacks 0GV8 "finite-dimensional closed-point fiber"]
#check @Module.ClosedFiber.finiteDimensional_of_finitePresentation

@[stacks 0GV8 "section image in a closed-point fiber"]
#check @Module.ClosedFiber.mk

#check @Module.ClosedFiber.residueFieldAlgEquiv
#check @Module.ClosedFiber.tensorEquiv
