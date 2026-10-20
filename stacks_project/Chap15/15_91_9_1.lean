/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.BeauvilleLaszlo.ModuleCech

import StacksCheckRecall

/-!
# The module Beauville-Laszlo Cech sequence

The explicit tensor-image construction and its transported maps are owned by
`ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.BeauvilleLaszlo.ModuleCech`.

@stack 0F1R
-/

universe u

open CategoryTheory

section

variable {R : Type u} [CommRing R]
variable (R' : Type u) [CommRing R'] [Algebra R R']
variable (M : Type u) [AddCommGroup M] [Module R M]
variable (f : R)

-- The two displayed maps in the module Cech sequence.
@[stacks 0F1R "the left map in 15.91.9.1"]
#check @beauvilleLaszloModuleCechAlpha

@[stacks 0F1R "the right map in 15.91.9.1"]
#check @beauvilleLaszloModuleCechBeta

-- 15.91.9.1: the displayed sequence is the canonical transported short complex.
@[stacks 0F1R "15.91.9.1"]
#check
  (beauvilleLaszloModuleCechSequence R' M f : ShortComplex (ModuleCat R))

end
