/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.CategoryTheory.Homology.DoubleComplex.HomotopyTotal
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape HomologicalComplex₂ HomotopyCategory

noncomputable section

universe v u

variable (A : Type u) [Category.{v} A] [Preadditive A]
  [HasZeroObject A] [HasBinaryBiproducts A] [HasCountableCoproducts A]

/- The first-direction convention is represented by flipped totalization. It commutes with
shifts. -/
#check (inferInstance : (HomotopyTotal.flipped A).CommShift ℤ)

/- Remark 13.10.8 (1): first-direction totalization is exact. -/
@[stacks 0G6D "first totalization is exact"] #check
  (inferInstance : (HomotopyTotal.flipped A).IsTriangulated)

/- The second-direction convention is represented by direct totalization. It commutes with
shifts. -/
#check (inferInstance : (HomotopyTotal.direct A).CommShift ℤ)

/- Remark 13.10.8 (2): second-direction totalization is exact. -/
@[stacks 0G6D "second totalization is exact"] #check
  (inferInstance : (HomotopyTotal.direct A).IsTriangulated)
