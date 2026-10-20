/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.LocalizedModule.Away.Cech.FormalGluing
import StacksCheckRecall

@[expose] public section

/-!
# Equation 15.90.8.1

@stack 05EJ
-/

-- Equation 15.90.8.1, the two explicit arrows in the formal-gluing module complex.
@[stacks 05EJ "Equation 15.90.8.1, first map"]
#check @LocalizedModule.Away.Cech.FormalGluing.alpha

@[stacks 05EJ "Equation 15.90.8.1, second map"]
#check @LocalizedModule.Away.Cech.FormalGluing.beta

-- Equation 15.90.8.1 as a short complex of `R`-modules.
@[stacks 05EJ "Equation 15.90.8.1, short complex"]
#check @LocalizedModule.Away.Cech.FormalGluing.complex
