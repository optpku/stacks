/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.CohenMacaulay.Fiber.Decomposition
import StacksCheckRecall

/-!
# Decomposition by pure fiber dimension

@stack 00RL
-/

@[expose] public section

@[stacks 00RL "structured decomposition by occurring fiber dimensions"]
#check @Algebra.CohenMacaulayFiber.Decomposition

@[stacks 00RL "the recorded dimensions are exactly the nonempty strata"]
#check @Algebra.CohenMacaulayFiber.Decomposition.mem_dimensions_iff

@[stacks 00RL "canonical quotient components of the product decomposition"]
#check @Algebra.CohenMacaulayFiber.Decomposition.equiv_apply

@[stacks 00RL "fiber strata cut out by the quotient ideals"]
#check @Algebra.CohenMacaulayFiber.Decomposition.stratum_eq_zeroLocus

@[stacks 00RL "independent Cohen-Macaulay, equidimensional, and dimension clauses"]
#check @Algebra.CohenMacaulayFiber.Decomposition.fiber_spec

@[stacks 00RL "complete source-facing specification"]
#check @Algebra.CohenMacaulayFiber.Decomposition.spec

@[stacks 00RL]
#check @Algebra.CohenMacaulayFiber.Decomposition.nonempty_of_finitePresentation_flat
