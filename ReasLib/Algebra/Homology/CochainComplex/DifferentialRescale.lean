module

public import ReasLib.Algebra.Homology.HomologicalComplex.DifferentialRescale.Linear
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Scaling the differential of a cochain complex

Multiplying every differential by the same scalar preserves the square-zero relation.  This file
packages that construction independently of the double-complex applications which motivate it.

@stack 0194
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v u w

namespace CategoryTheory.CochainComplex

variable {R : Type w} [Semiring R]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]

namespace rescaleDifferential

/-- Consecutive differentials remain square-zero after multiplication by a fixed scalar. -/
@[stacks 0194 "cochain specialization rescaling square-zero"]
theorem sq (K : CochainComplex C ℤ) (r : R) (n : ℤ) :
    (r • K.d n (n + 1)) ≫ (r • K.d (n + 1) (n + 1 + 1)) = 0 := sorry

end rescaleDifferential

/-- The cochain complex obtained by multiplying every differential by the scalar `r`. -/
@[stacks 0194 "cochain specialization differential rescaling"]
def rescaleDifferential (K : CochainComplex C ℤ) (r : R) :
    CochainComplex C ℤ :=
  HomologicalComplex.Rescale.ofLinear K (fun _ : ℤ ↦ r)

namespace rescaleDifferential

/-- Rescaling the differential does not change the objects of the complex. -/
@[simp, stacks 0194 "cochain specialization rescaling object formula"]
theorem X (K : CochainComplex C ℤ) (r : R) (n : ℤ) :
    (K.rescaleDifferential r).X n = K.X n := sorry

/-- The differential in the rescaled complex is the prescribed scalar multiple in every pair of
degrees. -/
@[simp, stacks 0194 "cochain specialization rescaling differential formula"]
theorem d (K : CochainComplex C ℤ) (r : R) (i j : ℤ) :
    (K.rescaleDifferential r).d i j = r • K.d i j := sorry

end rescaleDifferential

end CategoryTheory.CochainComplex
