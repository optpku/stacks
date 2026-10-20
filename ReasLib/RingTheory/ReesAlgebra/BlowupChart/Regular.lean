module

public import ReasLib.RingTheory.ReesAlgebra.BlowupChart.Localization

/-!
# Nonzerodivisors in affine blowup charts

Nonzerodivisors of the base ring remain nonzerodivisors after mapping to an
affine blowup chart.
-/

@[expose] public section

noncomputable section

open scoped nonZeroDivisors

universe u

namespace AffineBlowupChart

variable {A : Type u} [CommRing A]

/-- A nonzerodivisor of the base ring remains a nonzerodivisor in every affine blowup chart. -/
theorem algebraMap_mem_nonZeroDivisors (I : Ideal A) (a : I) (x : A)
    (hx : x ∈ nonZeroDivisors A) :
    AffineBlowupChart.algebraMap I a x ∈
      nonZeroDivisors (affineBlowupChart I a) := sorry

end AffineBlowupChart
