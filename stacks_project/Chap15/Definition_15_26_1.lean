/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.ReesAlgebra.BlowupChart.StrictTransform
import StacksCheckRecall

/-!
# Definition 15.26.1

@stack 053H

The strict transform and its canonical module structures are owned by the reusable affine
blowup-chart API.
-/

@[expose] public section

/- Definition 15.26.1: the strict transform is the quotient of the chartwise tensor product by
the power-torsion primary component of the distinguished chart parameter. -/
@[stacks 053H "Definition 15.26.1"]
#check @AffineBlowupChart.strictTransform

open scoped AffineBlowupChart

noncomputable section

universe u v

variable {R : Type u} [CommRing R] (I : Ideal R) (a : I)
  (M : Type v) [AddCommGroup M] [Module R M]

example : AddCommGroup (AffineBlowupChart.strictTransform I a M) := inferInstance
example : Module R[I / a] (AffineBlowupChart.strictTransform I a M) := inferInstance
example : Module R (AffineBlowupChart.strictTransform I a M) := inferInstance

end
