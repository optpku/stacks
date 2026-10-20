/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.AdicCompletion.InverseSystem
import StacksCheckRecall

@[expose] public section

/-!
# Successive Ideal-Power Quotient Systems

The former chapter-local kernel-system construction is represented directly by
the shared successive-quotient inverse-system interface.

@stack 09B8
-/

@[stacks 09B8 "stagewise annihilation from successive kernels"]
#check @CategoryTheory.PNatInverseSystem.stagewise_annihilated_of_stepKernel

@[stacks 09B8 "bijectivity for successive ideal-power quotients"]
#check @CategoryTheory.PNatInverseSystem.limitProjectionQuotient_bijective_of_successiveIdealPowerQuotients
