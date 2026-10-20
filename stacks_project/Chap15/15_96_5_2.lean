/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.HomologicalComplex.Bockstein

@[expose] public section

/-! # 15.96.5.2 (0GSQ)

@stack 0GSQ

The Bockstein cohomology complex.
-/

open scoped nonZeroDivisors
open HomologicalComplex.Bockstein

noncomputable section

universe u v

section


variable {A : Type u} [CommRing A]
variable (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ)
variable (hf : f ∈ nonZeroDivisors A) (hK : K.IsTermwiseSMulRegular f)

/- 15.96.5.2, tag `0GSQ`: the cohomology modules of `K / fK`, with the Bockstein
operator as differential. -/
@[stacks 0GSQ "the Bockstein cohomology complex"]
#check complex f K hK

#check complex_X f K hK
#check complex_d f K hK
#check operator_sq f K hK

end
