/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.HomologicalComplex.Bockstein

@[expose] public section

/-!
# Lemma 15.96.7: vanishing of the Bockstein operator

@stack 0F7Y
-/

open scoped nonZeroDivisors
open HomologicalComplex.Bockstein

noncomputable section

universe u v

section


variable {A : Type u} [CommRing A]
variable (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ)
variable (hf : f ∈ nonZeroDivisors A) (hK : K.IsTermwiseSMulRegular f)

/- Lemma 15.96.7, tag `0F7Y` (1): cycles lift modulo `f²` exactly when the Bockstein operator
vanishes. -/
@[stacks 0F7Y "surjectivity on reduced cycles versus the Bockstein operator"]
#check cyclesLift_iff_operator_eq_zero
  f K hK i (i + 1) (ComplexShape.up_mk i (i + 1) rfl)

variable (hH : Submodule.torsionBy A (K.homology (i + 1)) f = ⊥)

/- Lemma 15.96.7, tag `0F7Y` (2): vanishing `f`-torsion in the next cohomology group implies
cycles lift modulo `f²`. -/
@[stacks 0F7Y "torsion-free cohomology implies surjectivity on reduced cycles"]
#check cyclesLift_of_torsionBy_eq_bot
  f K hK i (i + 1) (ComplexShape.up_mk i (i + 1) rfl) hH

end
