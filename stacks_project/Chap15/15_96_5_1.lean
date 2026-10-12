/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.HomologicalComplex.Bockstein

@[expose] public section

/-! # 15.96.5.1 (0GSP)

@stack 0GSP

Factorization of the Bockstein operator.
-/

open HomologicalComplex.Bockstein
open scoped nonZeroDivisors

noncomputable section

universe u v

section


variable {A : Type u} [CommRing A]
variable (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ)
variable (hf : f ∈ nonZeroDivisors A) (hK : K.IsTermwiseSMulRegular f)

/- 15.96.5.1, tag `0GSP`: the integral connecting morphism followed by reduction modulo `f`
is the Bockstein operator. -/
@[stacks 0GSP "factorization of the Bockstein operator"]
#check integralOperator_comp_reduction
  f K hK i (i + 1) (ComplexShape.up_mk i (i + 1) rfl)

/- The shared factorization theorem is the scalar-row specialization of mathlib's naturality of
connecting morphisms. -/
#check @HomologicalComplex.HomologySequence.δ_naturality

end
